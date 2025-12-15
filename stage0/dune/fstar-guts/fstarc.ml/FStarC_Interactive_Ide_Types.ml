open Prims
let initial_range (filename : Prims.string) : FStarC_Range_Type.range=
  let uu___ = FStarC_Range_Type.mk_pos Prims.int_one Prims.int_zero in
  let uu___1 = FStarC_Range_Type.mk_pos Prims.int_one Prims.int_zero in
  FStarC_Range_Type.mk_range filename uu___ uu___1
type push_kind =
  | SyntaxCheck 
  | LaxCheck 
  | FullCheck 
let uu___is_SyntaxCheck (projectee : push_kind) : Prims.bool=
  match projectee with | SyntaxCheck -> true | uu___ -> false
let uu___is_LaxCheck (projectee : push_kind) : Prims.bool=
  match projectee with | LaxCheck -> true | uu___ -> false
let uu___is_FullCheck (projectee : push_kind) : Prims.bool=
  match projectee with | FullCheck -> true | uu___ -> false
let showable_push_kind : push_kind FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | SyntaxCheck -> "SyntaxCheck"
         | LaxCheck -> "LaxCheck"
         | FullCheck -> "FullCheck")
  }
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let uu___is_CKCode (projectee : completion_context) : Prims.bool=
  match projectee with | CKCode -> true | uu___ -> false
let uu___is_CKOption (projectee : completion_context) : Prims.bool=
  match projectee with | CKOption _0 -> true | uu___ -> false
let __proj__CKOption__item___0 (projectee : completion_context) : Prims.bool=
  match projectee with | CKOption _0 -> _0
let uu___is_CKModuleOrNamespace (projectee : completion_context) :
  Prims.bool=
  match projectee with | CKModuleOrNamespace _0 -> true | uu___ -> false
let __proj__CKModuleOrNamespace__item___0 (projectee : completion_context) :
  (Prims.bool * Prims.bool)=
  match projectee with | CKModuleOrNamespace _0 -> _0
type lookup_context =
  | LKSymbolOnly 
  | LKModule 
  | LKOption 
  | LKCode 
let uu___is_LKSymbolOnly (projectee : lookup_context) : Prims.bool=
  match projectee with | LKSymbolOnly -> true | uu___ -> false
let uu___is_LKModule (projectee : lookup_context) : Prims.bool=
  match projectee with | LKModule -> true | uu___ -> false
let uu___is_LKOption (projectee : lookup_context) : Prims.bool=
  match projectee with | LKOption -> true | uu___ -> false
let uu___is_LKCode (projectee : lookup_context) : Prims.bool=
  match projectee with | LKCode -> true | uu___ -> false
type position = (Prims.string * Prims.int * Prims.int)
type push_query =
  {
  push_kind: push_kind ;
  push_line: Prims.int ;
  push_column: Prims.int ;
  push_peek_only: Prims.bool ;
  push_code_or_decl:
    (Prims.string,
      (FStarC_Parser_AST.decl * FStarC_Parser_ParseIt.code_fragment))
      FStar_Pervasives.either
    }
let __proj__Mkpush_query__item__push_kind (projectee : push_query) :
  push_kind=
  match projectee with
  | { push_kind = push_kind1; push_line; push_column; push_peek_only;
      push_code_or_decl;_} -> push_kind1
let __proj__Mkpush_query__item__push_line (projectee : push_query) :
  Prims.int=
  match projectee with
  | { push_kind = push_kind1; push_line; push_column; push_peek_only;
      push_code_or_decl;_} -> push_line
let __proj__Mkpush_query__item__push_column (projectee : push_query) :
  Prims.int=
  match projectee with
  | { push_kind = push_kind1; push_line; push_column; push_peek_only;
      push_code_or_decl;_} -> push_column
let __proj__Mkpush_query__item__push_peek_only (projectee : push_query) :
  Prims.bool=
  match projectee with
  | { push_kind = push_kind1; push_line; push_column; push_peek_only;
      push_code_or_decl;_} -> push_peek_only
let __proj__Mkpush_query__item__push_code_or_decl (projectee : push_query) :
  (Prims.string,
    (FStarC_Parser_AST.decl * FStarC_Parser_ParseIt.code_fragment))
    FStar_Pervasives.either=
  match projectee with
  | { push_kind = push_kind1; push_line; push_column; push_peek_only;
      push_code_or_decl;_} -> push_code_or_decl
type lookup_symbol_range = FStarC_Json.json
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol 
let uu___is_QueryOK (projectee : query_status) : Prims.bool=
  match projectee with | QueryOK -> true | uu___ -> false
let uu___is_QueryNOK (projectee : query_status) : Prims.bool=
  match projectee with | QueryNOK -> true | uu___ -> false
let uu___is_QueryViolatesProtocol (projectee : query_status) : Prims.bool=
  match projectee with | QueryViolatesProtocol -> true | uu___ -> false
type repl_depth_t = (FStarC_TypeChecker_Env.tcenv_depth_t * Prims.int)
type optmod_t = FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option
type timed_fname =
  {
  tf_fname: Prims.string ;
  tf_modtime: FStarC_Time.time_of_day }
let __proj__Mktimed_fname__item__tf_fname (projectee : timed_fname) :
  Prims.string= match projectee with | { tf_fname; tf_modtime;_} -> tf_fname
let __proj__Mktimed_fname__item__tf_modtime (projectee : timed_fname) :
  FStarC_Time.time_of_day=
  match projectee with | { tf_fname; tf_modtime;_} -> tf_modtime
type repl_task =
  | LDInterleaved of (timed_fname * timed_fname) 
  | LDSingle of timed_fname 
  | LDInterfaceOfCurrentFile of timed_fname 
  | PushFragment of ((FStarC_Parser_ParseIt.input_frag,
  FStarC_Parser_AST.decl) FStar_Pervasives.either * push_kind *
  FStarC_Json.json Prims.list * Prims.string Prims.list) 
  | Noop 
let uu___is_LDInterleaved (projectee : repl_task) : Prims.bool=
  match projectee with | LDInterleaved _0 -> true | uu___ -> false
let __proj__LDInterleaved__item___0 (projectee : repl_task) :
  (timed_fname * timed_fname)= match projectee with | LDInterleaved _0 -> _0
let uu___is_LDSingle (projectee : repl_task) : Prims.bool=
  match projectee with | LDSingle _0 -> true | uu___ -> false
let __proj__LDSingle__item___0 (projectee : repl_task) : timed_fname=
  match projectee with | LDSingle _0 -> _0
let uu___is_LDInterfaceOfCurrentFile (projectee : repl_task) : Prims.bool=
  match projectee with | LDInterfaceOfCurrentFile _0 -> true | uu___ -> false
let __proj__LDInterfaceOfCurrentFile__item___0 (projectee : repl_task) :
  timed_fname= match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let uu___is_PushFragment (projectee : repl_task) : Prims.bool=
  match projectee with | PushFragment _0 -> true | uu___ -> false
let __proj__PushFragment__item___0 (projectee : repl_task) :
  ((FStarC_Parser_ParseIt.input_frag, FStarC_Parser_AST.decl)
    FStar_Pervasives.either * push_kind * FStarC_Json.json Prims.list *
    Prims.string Prims.list)=
  match projectee with | PushFragment _0 -> _0
let uu___is_Noop (projectee : repl_task) : Prims.bool=
  match projectee with | Noop -> true | uu___ -> false
let t0 : FStarC_Time.time_of_day= FStarC_Time.get_time_of_day ()
let dummy_tf_of_fname (fname : Prims.string) : timed_fname=
  { tf_fname = fname; tf_modtime = t0 }
let mk_ld_interleaved (iface : Prims.string) (impl : Prims.string) :
  repl_task=
  let tod = FStarC_Time.get_time_of_day () in
  LDInterleaved
    ({ tf_fname = iface; tf_modtime = tod },
      { tf_fname = impl; tf_modtime = tod })
let mk_ld_single (filename : Prims.string) : repl_task=
  let tod = FStarC_Time.get_time_of_day () in
  LDSingle { tf_fname = filename; tf_modtime = tod }
type full_buffer_request_kind =
  | Full 
  | Lax 
  | Cache 
  | ReloadDeps 
  | VerifyToPosition of position 
  | LaxToPosition of position 
let uu___is_Full (projectee : full_buffer_request_kind) : Prims.bool=
  match projectee with | Full -> true | uu___ -> false
let uu___is_Lax (projectee : full_buffer_request_kind) : Prims.bool=
  match projectee with | Lax -> true | uu___ -> false
let uu___is_Cache (projectee : full_buffer_request_kind) : Prims.bool=
  match projectee with | Cache -> true | uu___ -> false
let uu___is_ReloadDeps (projectee : full_buffer_request_kind) : Prims.bool=
  match projectee with | ReloadDeps -> true | uu___ -> false
let uu___is_VerifyToPosition (projectee : full_buffer_request_kind) :
  Prims.bool=
  match projectee with | VerifyToPosition _0 -> true | uu___ -> false
let __proj__VerifyToPosition__item___0 (projectee : full_buffer_request_kind)
  : position= match projectee with | VerifyToPosition _0 -> _0
let uu___is_LaxToPosition (projectee : full_buffer_request_kind) :
  Prims.bool=
  match projectee with | LaxToPosition _0 -> true | uu___ -> false
let __proj__LaxToPosition__item___0 (projectee : full_buffer_request_kind) :
  position= match projectee with | LaxToPosition _0 -> _0
type query' =
  | Exit 
  | DescribeProtocol 
  | DescribeRepl 
  | Segment of Prims.string 
  | Pop 
  | Push of push_query 
  | PushPartialCheckedFile of Prims.string 
  | VfsAdd of (Prims.string FStar_Pervasives_Native.option * Prims.string) 
  | AutoComplete of (Prims.string * completion_context) 
  | Lookup of (Prims.string * lookup_context * position
  FStar_Pervasives_Native.option * Prims.string Prims.list *
  lookup_symbol_range FStar_Pervasives_Native.option) 
  | Compute of (Prims.string * FStarC_TypeChecker_Env.step Prims.list
  FStar_Pervasives_Native.option) 
  | Search of Prims.string 
  | GenericError of Prims.string 
  | ProtocolViolation of Prims.string 
  | FullBuffer of (Prims.string * full_buffer_request_kind * Prims.bool) 
  | Callback of
  (repl_state ->
     ((query_status * FStarC_Json.json Prims.list) * (repl_state, Prims.int)
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
  repl_env: FStarC_TypeChecker_Env.env ;
  repl_stdin: FStarC_Util.stream_reader ;
  repl_names: FStarC_Interactive_CompletionTable.table ;
  repl_buffered_input_queries: query Prims.list ;
  repl_lang: FStarC_Universal.lang_decls_t }
let uu___is_Exit (projectee : query') : Prims.bool=
  match projectee with | Exit -> true | uu___ -> false
let uu___is_DescribeProtocol (projectee : query') : Prims.bool=
  match projectee with | DescribeProtocol -> true | uu___ -> false
let uu___is_DescribeRepl (projectee : query') : Prims.bool=
  match projectee with | DescribeRepl -> true | uu___ -> false
let uu___is_Segment (projectee : query') : Prims.bool=
  match projectee with | Segment _0 -> true | uu___ -> false
let __proj__Segment__item___0 (projectee : query') : Prims.string=
  match projectee with | Segment _0 -> _0
let uu___is_Pop (projectee : query') : Prims.bool=
  match projectee with | Pop -> true | uu___ -> false
let uu___is_Push (projectee : query') : Prims.bool=
  match projectee with | Push _0 -> true | uu___ -> false
let __proj__Push__item___0 (projectee : query') : push_query=
  match projectee with | Push _0 -> _0
let uu___is_PushPartialCheckedFile (projectee : query') : Prims.bool=
  match projectee with | PushPartialCheckedFile _0 -> true | uu___ -> false
let __proj__PushPartialCheckedFile__item___0 (projectee : query') :
  Prims.string= match projectee with | PushPartialCheckedFile _0 -> _0
let uu___is_VfsAdd (projectee : query') : Prims.bool=
  match projectee with | VfsAdd _0 -> true | uu___ -> false
let __proj__VfsAdd__item___0 (projectee : query') :
  (Prims.string FStar_Pervasives_Native.option * Prims.string)=
  match projectee with | VfsAdd _0 -> _0
let uu___is_AutoComplete (projectee : query') : Prims.bool=
  match projectee with | AutoComplete _0 -> true | uu___ -> false
let __proj__AutoComplete__item___0 (projectee : query') :
  (Prims.string * completion_context)=
  match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup (projectee : query') : Prims.bool=
  match projectee with | Lookup _0 -> true | uu___ -> false
let __proj__Lookup__item___0 (projectee : query') :
  (Prims.string * lookup_context * position FStar_Pervasives_Native.option *
    Prims.string Prims.list * lookup_symbol_range
    FStar_Pervasives_Native.option)=
  match projectee with | Lookup _0 -> _0
let uu___is_Compute (projectee : query') : Prims.bool=
  match projectee with | Compute _0 -> true | uu___ -> false
let __proj__Compute__item___0 (projectee : query') :
  (Prims.string * FStarC_TypeChecker_Env.step Prims.list
    FStar_Pervasives_Native.option)=
  match projectee with | Compute _0 -> _0
let uu___is_Search (projectee : query') : Prims.bool=
  match projectee with | Search _0 -> true | uu___ -> false
let __proj__Search__item___0 (projectee : query') : Prims.string=
  match projectee with | Search _0 -> _0
let uu___is_GenericError (projectee : query') : Prims.bool=
  match projectee with | GenericError _0 -> true | uu___ -> false
let __proj__GenericError__item___0 (projectee : query') : Prims.string=
  match projectee with | GenericError _0 -> _0
let uu___is_ProtocolViolation (projectee : query') : Prims.bool=
  match projectee with | ProtocolViolation _0 -> true | uu___ -> false
let __proj__ProtocolViolation__item___0 (projectee : query') : Prims.string=
  match projectee with | ProtocolViolation _0 -> _0
let uu___is_FullBuffer (projectee : query') : Prims.bool=
  match projectee with | FullBuffer _0 -> true | uu___ -> false
let __proj__FullBuffer__item___0 (projectee : query') :
  (Prims.string * full_buffer_request_kind * Prims.bool)=
  match projectee with | FullBuffer _0 -> _0
let uu___is_Callback (projectee : query') : Prims.bool=
  match projectee with | Callback _0 -> true | uu___ -> false
let __proj__Callback__item___0 (projectee : query') :
  repl_state ->
    ((query_status * FStarC_Json.json Prims.list) * (repl_state, Prims.int)
      FStar_Pervasives.either)=
  match projectee with | Callback _0 -> _0
let uu___is_Format (projectee : query') : Prims.bool=
  match projectee with | Format _0 -> true | uu___ -> false
let __proj__Format__item___0 (projectee : query') : Prims.string=
  match projectee with | Format _0 -> _0
let uu___is_RestartSolver (projectee : query') : Prims.bool=
  match projectee with | RestartSolver -> true | uu___ -> false
let uu___is_Cancel (projectee : query') : Prims.bool=
  match projectee with | Cancel _0 -> true | uu___ -> false
let __proj__Cancel__item___0 (projectee : query') :
  position FStar_Pervasives_Native.option=
  match projectee with | Cancel _0 -> _0
let __proj__Mkquery__item__qq (projectee : query) : query'=
  match projectee with | { qq; qid;_} -> qq
let __proj__Mkquery__item__qid (projectee : query) : Prims.string=
  match projectee with | { qq; qid;_} -> qid
let __proj__Mkrepl_state__item__repl_line (projectee : repl_state) :
  Prims.int=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_line
let __proj__Mkrepl_state__item__repl_column (projectee : repl_state) :
  Prims.int=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_column
let __proj__Mkrepl_state__item__repl_fname (projectee : repl_state) :
  Prims.string=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_fname
let __proj__Mkrepl_state__item__repl_deps_stack (projectee : repl_state) :
  (repl_depth_t * (repl_task * repl_state)) Prims.list=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_deps_stack
let __proj__Mkrepl_state__item__repl_curmod (projectee : repl_state) :
  optmod_t=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_curmod
let __proj__Mkrepl_state__item__repl_env (projectee : repl_state) :
  FStarC_TypeChecker_Env.env=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_env
let __proj__Mkrepl_state__item__repl_stdin (projectee : repl_state) :
  FStarC_Util.stream_reader=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_stdin
let __proj__Mkrepl_state__item__repl_names (projectee : repl_state) :
  FStarC_Interactive_CompletionTable.table=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_names
let __proj__Mkrepl_state__item__repl_buffered_input_queries
  (projectee : repl_state) : query Prims.list=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_buffered_input_queries
let __proj__Mkrepl_state__item__repl_lang (projectee : repl_state) :
  FStarC_Universal.lang_decls_t=
  match projectee with
  | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
      repl_env; repl_stdin; repl_names; repl_buffered_input_queries;
      repl_lang;_} -> repl_lang
type callback_t =
  repl_state ->
    ((query_status * FStarC_Json.json Prims.list) * (repl_state, Prims.int)
      FStar_Pervasives.either)
type repl_stack_entry_t = (repl_depth_t * (repl_task * repl_state))
type repl_stack_t = (repl_depth_t * (repl_task * repl_state)) Prims.list
type grepl_state =
  {
  grepl_repls: repl_state FStarC_PSMap.t ;
  grepl_stdin: FStarC_Util.stream_reader }
let __proj__Mkgrepl_state__item__grepl_repls (projectee : grepl_state) :
  repl_state FStarC_PSMap.t=
  match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_repls
let __proj__Mkgrepl_state__item__grepl_stdin (projectee : grepl_state) :
  FStarC_Util.stream_reader=
  match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_stdin
let string_of_timed_fname (uu___ : timed_fname) : Prims.string=
  match uu___ with
  | { tf_fname = fname; tf_modtime = modtime;_} ->
      if modtime = t0
      then FStarC_Format.fmt1 "{ %s }" fname
      else
        (let uu___2 =
           FStarC_Class_Show.show
             { FStarC_Class_Show.show = FStarC_Time.string_of_time_of_day }
             modtime in
         FStarC_Format.fmt2 "{ %s; %s }" fname uu___2)
let string_of_repl_task (uu___ : repl_task) : Prims.string=
  match uu___ with
  | LDInterleaved (intf, impl) ->
      let uu___1 = string_of_timed_fname intf in
      let uu___2 = string_of_timed_fname impl in
      FStarC_Format.fmt2 "LDInterleaved (%s, %s)" uu___1 uu___2
  | LDSingle intf_or_impl ->
      let uu___1 = string_of_timed_fname intf_or_impl in
      FStarC_Format.fmt1 "LDSingle %s" uu___1
  | LDInterfaceOfCurrentFile intf ->
      let uu___1 = string_of_timed_fname intf in
      FStarC_Format.fmt1 "LDInterfaceOfCurrentFile %s" uu___1
  | PushFragment (FStar_Pervasives.Inl frag, uu___1, uu___2, uu___3) ->
      FStarC_Format.fmt1 "PushFragment { code = %s }"
        frag.FStarC_Parser_ParseIt.frag_text
  | PushFragment (FStar_Pervasives.Inr d, uu___1, uu___2, deps) ->
      let uu___3 = FStarC_Class_Show.show FStarC_Parser_AST.showable_decl d in
      let uu___4 =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
          deps in
      FStarC_Format.fmt2 "PushFragment { decl = %s; deps=%s }" uu___3 uu___4
  | Noop -> "Noop {}"
let string_of_repl_stack_entry (uu___ : repl_stack_entry_t) : Prims.string=
  match uu___ with
  | ((depth, i), (task, state)) ->
      let uu___1 =
        let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
        let uu___3 = let uu___4 = string_of_repl_task task in [uu___4] in
        uu___2 :: uu___3 in
      FStarC_Format.fmt "{depth=%s; task=%s}" uu___1
let string_of_repl_stack (s : repl_stack_entry_t Prims.list) : Prims.string=
  let uu___ = FStarC_List.map string_of_repl_stack_entry s in
  FStarC_String.concat ";\n\t\t" uu___
let repl_state_to_string (r : repl_state) : Prims.string=
  let uu___ =
    let uu___1 =
      FStarC_Class_Show.show FStarC_Class_Show.showable_int r.repl_line in
    let uu___2 =
      let uu___3 =
        FStarC_Class_Show.show FStarC_Class_Show.showable_int r.repl_column in
      let uu___4 =
        let uu___5 =
          let uu___6 =
            match r.repl_curmod with
            | FStar_Pervasives_Native.None -> "None"
            | FStar_Pervasives_Native.Some m ->
                FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
          let uu___7 =
            let uu___8 = string_of_repl_stack r.repl_deps_stack in
            let uu___9 =
              let uu___10 =
                let uu___11 =
                  FStarC_List.map (fun q -> q.qid)
                    r.repl_buffered_input_queries in
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_list
                     FStarC_Class_Show.showable_string) uu___11 in
              [uu___10] in
            uu___8 :: uu___9 in
          uu___6 :: uu___7 in
        (r.repl_fname) :: uu___5 in
      uu___3 :: uu___4 in
    uu___1 :: uu___2 in
  FStarC_Format.fmt
    "{\n\trepl_line=%s;\n\trepl_column=%s;\n\trepl_fname=%s;\n\trepl_cur_mod=%s;\n\t\\      \n      repl_deps_stack={%s}\nrepl_buffered_queries={%s}\n\n     }"
    uu___
let repl_stack_entry_t_showable :
  repl_stack_entry_t FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = string_of_repl_stack_entry }
let repl_state_showable : repl_state FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = repl_state_to_string }
let push_query_to_string (pq : push_query) : Prims.string=
  let code_or_decl =
    match pq.push_code_or_decl with
    | FStar_Pervasives.Inl code -> code
    | FStar_Pervasives.Inr (_decl, code) -> code.FStarC_Parser_ParseIt.code in
  let uu___ =
    let uu___1 = FStarC_Class_Show.show showable_push_kind pq.push_kind in
    let uu___2 =
      let uu___3 =
        FStarC_Class_Show.show FStarC_Class_Show.showable_int pq.push_line in
      let uu___4 =
        let uu___5 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            pq.push_column in
        let uu___6 =
          let uu___7 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_bool
              pq.push_peek_only in
          [uu___7; code_or_decl] in
        uu___5 :: uu___6 in
      uu___3 :: uu___4 in
    uu___1 :: uu___2 in
  FStarC_Format.fmt
    "{ push_kind = %s; push_line = %s; push_column = %s; push_peek_only = %s; push_code_or_decl = %s }"
    uu___
let query_to_string (q : query) : Prims.string=
  match q.qq with
  | Exit -> "Exit"
  | DescribeProtocol -> "DescribeProtocol"
  | DescribeRepl -> "DescribeRepl"
  | Segment uu___ -> "Segment"
  | Pop -> "Pop"
  | Push pq ->
      let uu___ =
        let uu___1 = push_query_to_string pq in Prims.strcat uu___1 ")" in
      Prims.strcat "(Push " uu___
  | PushPartialCheckedFile d ->
      Prims.strcat "(PushPartialCheckedFile " (Prims.strcat d ")")
  | VfsAdd uu___ -> "VfsAdd"
  | AutoComplete uu___ -> "AutoComplete"
  | Lookup (s, _lc, pos, features, _sr) ->
      let uu___ =
        match pos with
        | FStar_Pervasives_Native.None -> "None"
        | FStar_Pervasives_Native.Some (f, i, j) ->
            let uu___1 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
            let uu___2 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int j in
            FStarC_Format.fmt3 "(%s, %s, %s)" f uu___1 uu___2 in
      FStarC_Format.fmt3 "(Lookup %s %s [%s])" s uu___
        (FStarC_String.concat "; " features)
  | Compute uu___ -> "Compute"
  | Search uu___ -> "Search"
  | GenericError uu___ -> "GenericError"
  | ProtocolViolation uu___ -> "ProtocolViolation"
  | FullBuffer uu___ -> "FullBuffer"
  | Callback uu___ -> "Callback"
  | Format uu___ -> "Format"
  | RestartSolver -> "RestartSolver"
  | Cancel uu___ -> "Cancel"
let query_needs_current_module (uu___ : query') : Prims.bool=
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
  | PushPartialCheckedFile uu___1 -> false
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
let interactive_protocol_vernum : Prims.int= (Prims.of_int (3))
let interactive_protocol_features : Prims.string Prims.list=
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
  "push-partial-checked-file";
  "search";
  "segment";
  "vfs-add";
  "tactic-ranges";
  "interrupt";
  "progress";
  "full-buffer";
  "format";
  "restart-solver";
  "cancel";
  "fly-deps"]
let json_of_issue_level (i : FStarC_Errors.issue_level) : FStarC_Json.json=
  FStarC_Json.JsonStr
    (match i with
     | FStarC_Errors.ENotImplemented -> "not-implemented"
     | FStarC_Errors.EInfo -> "info"
     | FStarC_Errors.EWarning -> "warning"
     | FStarC_Errors.EError -> "error")
let json_of_issue (issue : FStarC_Errors.issue) : FStarC_Json.json=
  let r =
    FStarC_Option.map FStarC_Range_Ops.refind_range
      issue.FStarC_Errors.issue_range in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 = FStarC_Errors.format_issue' false issue in
            FStarC_Json.JsonStr uu___5 in
          ("message", uu___4) in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 =
                  match r with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some r1 ->
                      let uu___9 = FStarC_Range_Ops.json_of_use_range r1 in
                      [uu___9] in
                let uu___9 =
                  match r with
                  | FStar_Pervasives_Native.Some r1 when
                      let uu___10 = FStarC_Range_Type.def_range r1 in
                      let uu___11 = FStarC_Range_Type.use_range r1 in
                      uu___10 <> uu___11 ->
                      let uu___10 = FStarC_Range_Ops.json_of_def_range r1 in
                      [uu___10]
                  | uu___10 -> [] in
                FStarC_List.op_At uu___8 uu___9 in
              FStarC_Json.JsonList uu___7 in
            ("ranges", uu___6) in
          [uu___5] in
        uu___3 :: uu___4 in
      FStarC_List.op_At
        (match issue.FStarC_Errors.issue_number with
         | FStar_Pervasives_Native.None -> []
         | FStar_Pervasives_Native.Some n ->
             [("number", (FStarC_Json.JsonInt n))]) uu___2 in
    FStarC_List.op_At
      [("level", (json_of_issue_level issue.FStarC_Errors.issue_level))]
      uu___1 in
  FStarC_Json.JsonAssoc uu___
let js_pushkind (s : FStarC_Json.json) : push_kind=
  let uu___ = FStarC_Interactive_JsonHelper.js_str s in
  match uu___ with
  | "syntax" -> SyntaxCheck
  | "lax" -> LaxCheck
  | "full" -> FullCheck
  | uu___1 -> FStarC_Interactive_JsonHelper.js_fail "push_kind" s
let js_reductionrule (s : FStarC_Json.json) : FStarC_TypeChecker_Env.step=
  let uu___ = FStarC_Interactive_JsonHelper.js_str s in
  match uu___ with
  | "beta" -> FStarC_TypeChecker_Env.Beta
  | "delta" ->
      FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant
  | "iota" -> FStarC_TypeChecker_Env.Iota
  | "zeta" -> FStarC_TypeChecker_Env.Zeta
  | "reify" -> FStarC_TypeChecker_Env.Reify
  | "pure-subterms" -> FStarC_TypeChecker_Env.PureSubtermsWithinComputations
  | uu___1 -> FStarC_Interactive_JsonHelper.js_fail "reduction rule" s
let js_optional_completion_context
  (k : FStarC_Json.json FStar_Pervasives_Native.option) : completion_context=
  match k with
  | FStar_Pervasives_Native.None -> CKCode
  | FStar_Pervasives_Native.Some k1 ->
      let uu___ = FStarC_Interactive_JsonHelper.js_str k1 in
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
           FStarC_Interactive_JsonHelper.js_fail
             "completion context (code, set-options, reset-options, open, let-open, include, module-alias)"
             k1)
let js_optional_lookup_context
  (k : FStarC_Json.json FStar_Pervasives_Native.option) : lookup_context=
  match k with
  | FStar_Pervasives_Native.None -> LKSymbolOnly
  | FStar_Pervasives_Native.Some k1 ->
      let uu___ = FStarC_Interactive_JsonHelper.js_str k1 in
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
           FStarC_Interactive_JsonHelper.js_fail
             "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)"
             k1)
