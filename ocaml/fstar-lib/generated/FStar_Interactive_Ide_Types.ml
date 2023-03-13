open Prims
let (initial_range : FStar_Compiler_Range.range) =
  let uu___ = FStar_Compiler_Range.mk_pos Prims.int_one Prims.int_zero in
  let uu___1 = FStar_Compiler_Range.mk_pos Prims.int_one Prims.int_zero in
  FStar_Compiler_Range.mk_range "<input>" uu___ uu___1
let (js_pushkind :
  FStar_Compiler_Util.json -> FStar_Interactive_PushHelper.push_kind) =
  fun s ->
    let uu___ = FStar_Interactive_JsonHelper.js_str s in
    match uu___ with
    | "syntax" -> FStar_Interactive_PushHelper.SyntaxCheck
    | "lax" -> FStar_Interactive_PushHelper.LaxCheck
    | "full" -> FStar_Interactive_PushHelper.FullCheck
    | uu___1 -> FStar_Interactive_JsonHelper.js_fail "push_kind" s
let (js_reductionrule :
  FStar_Compiler_Util.json -> FStar_TypeChecker_Env.step) =
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
let (js_optional_completion_context :
  FStar_Compiler_Util.json FStar_Pervasives_Native.option ->
    completion_context)
  =
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
let (js_optional_lookup_context :
  FStar_Compiler_Util.json FStar_Pervasives_Native.option -> lookup_context)
  =
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
type position = (Prims.string * Prims.int * Prims.int)
type push_query =
  {
  push_kind: FStar_Interactive_PushHelper.push_kind ;
  push_line: Prims.int ;
  push_column: Prims.int ;
  push_peek_only: Prims.bool ;
  push_code_or_decl:
    (Prims.string, FStar_Parser_AST.decl) FStar_Pervasives.either }
let (__proj__Mkpush_query__item__push_kind :
  push_query -> FStar_Interactive_PushHelper.push_kind) =
  fun projectee ->
    match projectee with
    | { push_kind; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_kind
let (__proj__Mkpush_query__item__push_line : push_query -> Prims.int) =
  fun projectee ->
    match projectee with
    | { push_kind; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_line
let (__proj__Mkpush_query__item__push_column : push_query -> Prims.int) =
  fun projectee ->
    match projectee with
    | { push_kind; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_column
let (__proj__Mkpush_query__item__push_peek_only : push_query -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { push_kind; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_peek_only
let (__proj__Mkpush_query__item__push_code_or_decl :
  push_query -> (Prims.string, FStar_Parser_AST.decl) FStar_Pervasives.either)
  =
  fun projectee ->
    match projectee with
    | { push_kind; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_code_or_decl
type lookup_symbol_range = FStar_Compiler_Util.json
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
  | FullBuffer of (Prims.string * Prims.bool) 
and query = {
  qq: query' ;
  qid: Prims.string }
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
let (__proj__FullBuffer__item___0 : query' -> (Prims.string * Prims.bool)) =
  fun projectee -> match projectee with | FullBuffer _0 -> _0
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee -> match projectee with | { qq; qid;_} -> qq
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee -> match projectee with | { qq; qid;_} -> qid
let (push_query_to_string : push_query -> Prims.string) =
  fun pq ->
    let pk =
      match pq.push_kind with
      | FStar_Interactive_PushHelper.SyntaxCheck -> "SyntaxCheck"
      | FStar_Interactive_PushHelper.LaxCheck -> "LaxCheck"
      | FStar_Interactive_PushHelper.FullCheck -> "FullCheck" in
    let code_or_decl =
      match pq.push_code_or_decl with
      | FStar_Pervasives.Inl code -> code
      | FStar_Pervasives.Inr decl -> FStar_Parser_AST.decl_to_string decl in
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
    | Lookup uu___ -> "Lookup"
    | Compute uu___ -> "Compute"
    | Search uu___ -> "Search"
    | GenericError uu___ -> "GenericError"
    | ProtocolViolation uu___ -> "ProtocolViolation"
    | FullBuffer uu___ -> "FullBuffer"
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
  "full-buffer"]
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
let (json_of_issue_level :
  FStar_Errors.issue_level -> FStar_Compiler_Util.json) =
  fun i ->
    FStar_Compiler_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented -> "not-implemented"
       | FStar_Errors.EInfo -> "info"
       | FStar_Errors.EWarning -> "warning"
       | FStar_Errors.EError -> "error")
let (json_of_issue : FStar_Errors.issue -> FStar_Compiler_Util.json) =
  fun issue ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStar_Errors.issue_message issue in
              FStar_Compiler_Util.JsonStr uu___5 in
            ("message", uu___4) in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.None -> []
                    | FStar_Pervasives_Native.Some r ->
                        let uu___9 = FStar_Compiler_Range.json_of_use_range r in
                        [uu___9] in
                  let uu___9 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.Some r when
                        let uu___10 = FStar_Compiler_Range.def_range r in
                        let uu___11 = FStar_Compiler_Range.use_range r in
                        uu___10 <> uu___11 ->
                        let uu___10 =
                          FStar_Compiler_Range.json_of_def_range r in
                        [uu___10]
                    | uu___10 -> [] in
                  FStar_Compiler_List.op_At uu___8 uu___9 in
                FStar_Compiler_Util.JsonList uu___7 in
              ("ranges", uu___6) in
            [uu___5] in
          uu___3 :: uu___4 in
        FStar_Compiler_List.op_At
          (match issue.FStar_Errors.issue_number with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some n ->
               [("number", (FStar_Compiler_Util.JsonInt n))]) uu___2 in
      FStar_Compiler_List.op_At
        [("level", (json_of_issue_level issue.FStar_Errors.issue_level))]
        uu___1 in
    FStar_Compiler_Effect.op_Less_Bar
      (fun uu___1 -> FStar_Compiler_Util.JsonAssoc uu___1) uu___