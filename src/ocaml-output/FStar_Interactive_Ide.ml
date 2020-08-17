open Prims
let with_captured_errors' :
  'uuuuuu28 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'uuuuuu28 FStar_Pervasives_Native.option)
          -> 'uuuuuu28 FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        try
          (fun uu___11_58 ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu____64 -> f env)) ()
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
            ((let uu____75 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.log_issue uu____75
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e, msg, r) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e, msg) ->
            ((let uu____96 =
                let uu____105 =
                  let uu____112 = FStar_TypeChecker_Env.get_range env in
                  (e, msg, uu____112) in
                [uu____105] in
              FStar_TypeChecker_Err.add_errors env uu____96);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop -> FStar_Pervasives_Native.None
let with_captured_errors :
  'uuuuuu133 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'uuuuuu133 FStar_Pervasives_Native.option)
          -> 'uuuuuu133 FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        let uu____160 = FStar_Options.trace_error () in
        if uu____160
        then f env
        else with_captured_errors' env sigint_handler f
let (t0 : FStar_Util.time) = FStar_Util.now ()
let (dummy_tf_of_fname :
  Prims.string -> FStar_Interactive_JsonHelper.timed_fname) =
  fun fname ->
    {
      FStar_Interactive_JsonHelper.tf_fname = fname;
      FStar_Interactive_JsonHelper.tf_modtime = t0
    }
let (string_of_timed_fname :
  FStar_Interactive_JsonHelper.timed_fname -> Prims.string) =
  fun uu____173 ->
    match uu____173 with
    | { FStar_Interactive_JsonHelper.tf_fname = fname;
        FStar_Interactive_JsonHelper.tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____177 = FStar_Util.string_of_time modtime in
           FStar_Util.format2 "{ %s; %s }" fname uu____177)
type push_query =
  {
  push_kind: FStar_Interactive_PushHelper.push_kind ;
  push_code: Prims.string ;
  push_line: Prims.int ;
  push_column: Prims.int ;
  push_peek_only: Prims.bool }
let (__proj__Mkpush_query__item__push_kind :
  push_query -> FStar_Interactive_PushHelper.push_kind) =
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
let (nothing_left_to_pop :
  FStar_Interactive_JsonHelper.repl_state -> Prims.bool) =
  fun st ->
    let uu____264 =
      let uu____265 =
        FStar_ST.op_Bang FStar_Interactive_PushHelper.repl_stack in
      FStar_List.length uu____265 in
    uu____264 =
      (FStar_List.length st.FStar_Interactive_JsonHelper.repl_deps_stack)
let (string_of_repl_task :
  FStar_Interactive_JsonHelper.repl_task -> Prims.string) =
  fun uu___0_302 ->
    match uu___0_302 with
    | FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) ->
        let uu____305 = string_of_timed_fname intf in
        let uu____306 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____305 uu____306
    | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
        let uu____308 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu____308
    | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu____310 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____310
    | FStar_Interactive_JsonHelper.PushFragment frag ->
        FStar_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
    | FStar_Interactive_JsonHelper.Noop -> "Noop {}"
let (run_repl_transaction :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Interactive_PushHelper.push_kind ->
      Prims.bool ->
        FStar_Interactive_JsonHelper.repl_task ->
          (Prims.bool * FStar_Interactive_JsonHelper.repl_state))
  =
  fun st ->
    fun push_kind ->
      fun must_rollback ->
        fun task ->
          let st1 =
            FStar_Interactive_PushHelper.push_repl "run_repl_transaction"
              push_kind task st in
          let uu____337 =
            FStar_Interactive_PushHelper.track_name_changes
              st1.FStar_Interactive_JsonHelper.repl_env in
          match uu____337 with
          | (env, finish_name_tracking) ->
              let check_success uu____380 =
                (let uu____383 = FStar_Errors.get_err_count () in
                 uu____383 = Prims.int_zero) &&
                  (Prims.op_Negation must_rollback) in
              let uu____384 =
                let uu____391 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1 ->
                       let uu____405 =
                         FStar_Interactive_PushHelper.run_repl_task
                           st1.FStar_Interactive_JsonHelper.repl_curmod env1
                           task in
                       FStar_All.pipe_left
                         (fun uu____424 ->
                            FStar_Pervasives_Native.Some uu____424) uu____405) in
                match uu____391 with
                | FStar_Pervasives_Native.Some (curmod, env1) when
                    check_success () -> (curmod, env1, true)
                | uu____437 ->
                    ((st1.FStar_Interactive_JsonHelper.repl_curmod), env,
                      false) in
              (match uu____384 with
               | (curmod, env1, success) ->
                   let uu____451 = finish_name_tracking env1 in
                   (match uu____451 with
                    | (env2, name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___95_470 = st1 in
                              {
                                FStar_Interactive_JsonHelper.repl_line =
                                  (uu___95_470.FStar_Interactive_JsonHelper.repl_line);
                                FStar_Interactive_JsonHelper.repl_column =
                                  (uu___95_470.FStar_Interactive_JsonHelper.repl_column);
                                FStar_Interactive_JsonHelper.repl_fname =
                                  (uu___95_470.FStar_Interactive_JsonHelper.repl_fname);
                                FStar_Interactive_JsonHelper.repl_deps_stack
                                  =
                                  (uu___95_470.FStar_Interactive_JsonHelper.repl_deps_stack);
                                FStar_Interactive_JsonHelper.repl_curmod =
                                  curmod;
                                FStar_Interactive_JsonHelper.repl_env = env2;
                                FStar_Interactive_JsonHelper.repl_stdin =
                                  (uu___95_470.FStar_Interactive_JsonHelper.repl_stdin);
                                FStar_Interactive_JsonHelper.repl_names =
                                  (uu___95_470.FStar_Interactive_JsonHelper.repl_names)
                              } in
                            FStar_Interactive_PushHelper.commit_name_tracking
                              st2 name_events
                          else
                            FStar_Interactive_PushHelper.pop_repl
                              "run_repl_transaction" st1 in
                        (success, st2)))
let (run_repl_ld_transactions :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Interactive_JsonHelper.repl_task Prims.list ->
      (FStar_Interactive_JsonHelper.repl_task -> unit) ->
        (FStar_Interactive_JsonHelper.repl_state,
          FStar_Interactive_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st ->
    fun tasks ->
      fun progress_callback ->
        let debug verb task =
          let uu____511 = FStar_Options.debug_any () in
          if uu____511
          then
            let uu____512 = string_of_repl_task task in
            FStar_Util.print2 "%s %s" verb uu____512
          else () in
        let rec revert_many st1 uu___1_534 =
          match uu___1_534 with
          | [] -> st1
          | (_id, (task, _st'))::entries ->
              (debug "Reverting" task;
               (let st' =
                  FStar_Interactive_PushHelper.pop_repl
                    "run_repl_ls_transactions" st1 in
                let dep_graph =
                  FStar_TypeChecker_Env.dep_graph
                    st1.FStar_Interactive_JsonHelper.repl_env in
                let st'1 =
                  let uu___121_585 = st' in
                  let uu____586 =
                    FStar_TypeChecker_Env.set_dep_graph
                      st'.FStar_Interactive_JsonHelper.repl_env dep_graph in
                  {
                    FStar_Interactive_JsonHelper.repl_line =
                      (uu___121_585.FStar_Interactive_JsonHelper.repl_line);
                    FStar_Interactive_JsonHelper.repl_column =
                      (uu___121_585.FStar_Interactive_JsonHelper.repl_column);
                    FStar_Interactive_JsonHelper.repl_fname =
                      (uu___121_585.FStar_Interactive_JsonHelper.repl_fname);
                    FStar_Interactive_JsonHelper.repl_deps_stack =
                      (uu___121_585.FStar_Interactive_JsonHelper.repl_deps_stack);
                    FStar_Interactive_JsonHelper.repl_curmod =
                      (uu___121_585.FStar_Interactive_JsonHelper.repl_curmod);
                    FStar_Interactive_JsonHelper.repl_env = uu____586;
                    FStar_Interactive_JsonHelper.repl_stdin =
                      (uu___121_585.FStar_Interactive_JsonHelper.repl_stdin);
                    FStar_Interactive_JsonHelper.repl_names =
                      (uu___121_585.FStar_Interactive_JsonHelper.repl_names)
                  } in
                revert_many st'1 entries)) in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([], []) -> FStar_Util.Inl st1
          | (task::tasks2, []) ->
              (debug "Loading" task;
               progress_callback task;
               (let uu____638 = FStar_Options.restore_cmd_line_options false in
                FStar_All.pipe_right uu____638 (fun uu____639 -> ()));
               (let timestamped_task =
                  FStar_Interactive_PushHelper.update_task_timestamps task in
                let push_kind =
                  let uu____642 = FStar_Options.lax () in
                  if uu____642
                  then FStar_Interactive_PushHelper.LaxCheck
                  else FStar_Interactive_PushHelper.FullCheck in
                let uu____644 =
                  run_repl_transaction st1 push_kind false timestamped_task in
                match uu____644 with
                | (success, st2) ->
                    if success
                    then
                      let uu____659 =
                        let uu___146_660 = st2 in
                        let uu____661 =
                          FStar_ST.op_Bang
                            FStar_Interactive_PushHelper.repl_stack in
                        {
                          FStar_Interactive_JsonHelper.repl_line =
                            (uu___146_660.FStar_Interactive_JsonHelper.repl_line);
                          FStar_Interactive_JsonHelper.repl_column =
                            (uu___146_660.FStar_Interactive_JsonHelper.repl_column);
                          FStar_Interactive_JsonHelper.repl_fname =
                            (uu___146_660.FStar_Interactive_JsonHelper.repl_fname);
                          FStar_Interactive_JsonHelper.repl_deps_stack =
                            uu____661;
                          FStar_Interactive_JsonHelper.repl_curmod =
                            (uu___146_660.FStar_Interactive_JsonHelper.repl_curmod);
                          FStar_Interactive_JsonHelper.repl_env =
                            (uu___146_660.FStar_Interactive_JsonHelper.repl_env);
                          FStar_Interactive_JsonHelper.repl_stdin =
                            (uu___146_660.FStar_Interactive_JsonHelper.repl_stdin);
                          FStar_Interactive_JsonHelper.repl_names =
                            (uu___146_660.FStar_Interactive_JsonHelper.repl_names)
                        } in
                      aux uu____659 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2, prev::previous1) when
              let uu____691 =
                FStar_Interactive_PushHelper.update_task_timestamps task in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____691
              -> (debug "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2, previous1) ->
              let uu____707 = revert_many st1 previous1 in
              aux uu____707 tasks2 [] in
        aux st tasks
          (FStar_List.rev st.FStar_Interactive_JsonHelper.repl_deps_stack)
let (js_pushkind : FStar_Util.json -> FStar_Interactive_PushHelper.push_kind)
  =
  fun s ->
    let uu____721 = FStar_Interactive_JsonHelper.js_str s in
    match uu____721 with
    | "syntax" -> FStar_Interactive_PushHelper.SyntaxCheck
    | "lax" -> FStar_Interactive_PushHelper.LaxCheck
    | "full" -> FStar_Interactive_PushHelper.FullCheck
    | uu____722 -> FStar_Interactive_JsonHelper.js_fail "push_kind" s
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s ->
    let uu____728 = FStar_Interactive_JsonHelper.js_str s in
    match uu____728 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____729 -> FStar_Interactive_JsonHelper.js_fail "reduction rule" s
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKCode -> true | uu____749 -> false
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKOption _0 -> true | uu____756 -> false
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKOption _0 -> _0
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____773 -> false
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee -> match projectee with | CKModuleOrNamespace _0 -> _0
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____802 = FStar_Interactive_JsonHelper.js_str k1 in
        (match uu____802 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____803 ->
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
    match projectee with | LKSymbolOnly -> true | uu____809 -> false
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKModule -> true | uu____815 -> false
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKOption -> true | uu____821 -> false
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee -> match projectee with | LKCode -> true | uu____827 -> false
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____838 = FStar_Interactive_JsonHelper.js_str k1 in
        (match uu____838 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____839 ->
             FStar_Interactive_JsonHelper.js_fail
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
  fun projectee -> match projectee with | Exit -> true | uu____936 -> false
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeProtocol -> true | uu____942 -> false
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeRepl -> true | uu____948 -> false
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Segment _0 -> true | uu____955 -> false
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Segment _0 -> _0
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee -> match projectee with | Pop -> true | uu____967 -> false
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Push _0 -> true | uu____974 -> false
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | VfsAdd _0 -> true | uu____993 -> false
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee -> match projectee with | VfsAdd _0 -> _0
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | AutoComplete _0 -> true | uu____1028 -> false
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee -> match projectee with | AutoComplete _0 -> _0
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Lookup _0 -> true | uu____1065 -> false
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee -> match projectee with | Lookup _0 -> _0
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Compute _0 -> true | uu____1122 -> false
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Compute _0 -> _0
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Search _0 -> true | uu____1159 -> false
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Search _0 -> _0
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | GenericError _0 -> true | uu____1172 -> false
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | GenericError _0 -> _0
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | ProtocolViolation _0 -> true | uu____1185 -> false
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | ProtocolViolation _0 -> _0
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee -> match projectee with | { qq; qid;_} -> qq
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee -> match projectee with | { qq; qid;_} -> qid
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___2_1210 ->
    match uu___2_1210 with
    | Exit -> false
    | DescribeProtocol -> false
    | DescribeRepl -> false
    | Segment uu____1211 -> false
    | Pop -> false
    | Push
        { push_kind = uu____1212; push_code = uu____1213;
          push_line = uu____1214; push_column = uu____1215;
          push_peek_only = false;_}
        -> false
    | VfsAdd uu____1216 -> false
    | GenericError uu____1223 -> false
    | ProtocolViolation uu____1224 -> false
    | Push uu____1225 -> true
    | AutoComplete uu____1226 -> true
    | Lookup uu____1231 -> true
    | Compute uu____1244 -> true
    | Search uu____1253 -> true
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
  "progress"]
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol 
let (uu___is_QueryOK : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryOK -> true | uu____1261 -> false
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryNOK -> true | uu____1267 -> false
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with
    | QueryViolatesProtocol -> true
    | uu____1273 -> false
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____1289 =
          let uu____1290 =
            let uu____1291 = FStar_Interactive_JsonHelper.json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1291 in
          ProtocolViolation uu____1290 in
        { qq = uu____1289; qid }
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json ->
    let assoc errloc key a =
      let uu____1313 = FStar_Interactive_JsonHelper.try_assoc key a in
      match uu____1313 with
      | FStar_Pervasives_Native.Some v -> v
      | FStar_Pervasives_Native.None ->
          let uu____1317 =
            let uu____1318 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            FStar_Interactive_JsonHelper.InvalidQuery uu____1318 in
          FStar_Exn.raise uu____1317 in
    let request =
      FStar_All.pipe_right json FStar_Interactive_JsonHelper.js_assoc in
    let qid =
      let uu____1321 = assoc "query" "query-id" request in
      FStar_All.pipe_right uu____1321 FStar_Interactive_JsonHelper.js_str in
    try
      (fun uu___259_1328 ->
         match () with
         | () ->
             let query1 =
               let uu____1330 = assoc "query" "query" request in
               FStar_All.pipe_right uu____1330
                 FStar_Interactive_JsonHelper.js_str in
             let args =
               let uu____1332 = assoc "query" "args" request in
               FStar_All.pipe_right uu____1332
                 FStar_Interactive_JsonHelper.js_assoc in
             let arg k = assoc "[args]" k args in
             let try_arg k =
               let uu____1347 = FStar_Interactive_JsonHelper.try_assoc k args in
               match uu____1347 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull) ->
                   FStar_Pervasives_Native.None
               | other -> other in
             let uu____1355 =
               match query1 with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____1356 =
                     let uu____1357 = arg "code" in
                     FStar_All.pipe_right uu____1357
                       FStar_Interactive_JsonHelper.js_str in
                   Segment uu____1356
               | "peek" ->
                   let uu____1358 =
                     let uu____1359 =
                       let uu____1360 = arg "kind" in
                       FStar_All.pipe_right uu____1360 js_pushkind in
                     let uu____1361 =
                       let uu____1362 = arg "code" in
                       FStar_All.pipe_right uu____1362
                         FStar_Interactive_JsonHelper.js_str in
                     let uu____1363 =
                       let uu____1364 = arg "line" in
                       FStar_All.pipe_right uu____1364
                         FStar_Interactive_JsonHelper.js_int in
                     let uu____1365 =
                       let uu____1366 = arg "column" in
                       FStar_All.pipe_right uu____1366
                         FStar_Interactive_JsonHelper.js_int in
                     {
                       push_kind = uu____1359;
                       push_code = uu____1361;
                       push_line = uu____1363;
                       push_column = uu____1365;
                       push_peek_only = (query1 = "peek")
                     } in
                   Push uu____1358
               | "push" ->
                   let uu____1367 =
                     let uu____1368 =
                       let uu____1369 = arg "kind" in
                       FStar_All.pipe_right uu____1369 js_pushkind in
                     let uu____1370 =
                       let uu____1371 = arg "code" in
                       FStar_All.pipe_right uu____1371
                         FStar_Interactive_JsonHelper.js_str in
                     let uu____1372 =
                       let uu____1373 = arg "line" in
                       FStar_All.pipe_right uu____1373
                         FStar_Interactive_JsonHelper.js_int in
                     let uu____1374 =
                       let uu____1375 = arg "column" in
                       FStar_All.pipe_right uu____1375
                         FStar_Interactive_JsonHelper.js_int in
                     {
                       push_kind = uu____1368;
                       push_code = uu____1370;
                       push_line = uu____1372;
                       push_column = uu____1374;
                       push_peek_only = (query1 = "peek")
                     } in
                   Push uu____1367
               | "autocomplete" ->
                   let uu____1376 =
                     let uu____1381 =
                       let uu____1382 = arg "partial-symbol" in
                       FStar_All.pipe_right uu____1382
                         FStar_Interactive_JsonHelper.js_str in
                     let uu____1383 =
                       let uu____1384 = try_arg "context" in
                       FStar_All.pipe_right uu____1384
                         js_optional_completion_context in
                     (uu____1381, uu____1383) in
                   AutoComplete uu____1376
               | "lookup" ->
                   let uu____1389 =
                     let uu____1402 =
                       let uu____1403 = arg "symbol" in
                       FStar_All.pipe_right uu____1403
                         FStar_Interactive_JsonHelper.js_str in
                     let uu____1404 =
                       let uu____1405 = try_arg "context" in
                       FStar_All.pipe_right uu____1405
                         js_optional_lookup_context in
                     let uu____1410 =
                       let uu____1413 =
                         let uu____1416 = try_arg "location" in
                         FStar_All.pipe_right uu____1416
                           (FStar_Util.map_option
                              FStar_Interactive_JsonHelper.js_assoc) in
                       FStar_All.pipe_right uu____1413
                         (FStar_Util.map_option
                            (fun loc ->
                               let uu____1438 =
                                 let uu____1439 =
                                   assoc "[location]" "filename" loc in
                                 FStar_All.pipe_right uu____1439
                                   FStar_Interactive_JsonHelper.js_str in
                               let uu____1440 =
                                 let uu____1441 =
                                   assoc "[location]" "line" loc in
                                 FStar_All.pipe_right uu____1441
                                   FStar_Interactive_JsonHelper.js_int in
                               let uu____1442 =
                                 let uu____1443 =
                                   assoc "[location]" "column" loc in
                                 FStar_All.pipe_right uu____1443
                                   FStar_Interactive_JsonHelper.js_int in
                               (uu____1438, uu____1440, uu____1442))) in
                     let uu____1444 =
                       let uu____1447 = arg "requested-info" in
                       FStar_All.pipe_right uu____1447
                         (FStar_Interactive_JsonHelper.js_list
                            FStar_Interactive_JsonHelper.js_str) in
                     (uu____1402, uu____1404, uu____1410, uu____1444) in
                   Lookup uu____1389
               | "compute" ->
                   let uu____1454 =
                     let uu____1463 =
                       let uu____1464 = arg "term" in
                       FStar_All.pipe_right uu____1464
                         FStar_Interactive_JsonHelper.js_str in
                     let uu____1465 =
                       let uu____1470 = try_arg "rules" in
                       FStar_All.pipe_right uu____1470
                         (FStar_Util.map_option
                            (FStar_Interactive_JsonHelper.js_list
                               js_reductionrule)) in
                     (uu____1463, uu____1465) in
                   Compute uu____1454
               | "search" ->
                   let uu____1485 =
                     let uu____1486 = arg "terms" in
                     FStar_All.pipe_right uu____1486
                       FStar_Interactive_JsonHelper.js_str in
                   Search uu____1485
               | "vfs-add" ->
                   let uu____1487 =
                     let uu____1494 =
                       let uu____1497 = try_arg "filename" in
                       FStar_All.pipe_right uu____1497
                         (FStar_Util.map_option
                            FStar_Interactive_JsonHelper.js_str) in
                     let uu____1504 =
                       let uu____1505 = arg "contents" in
                       FStar_All.pipe_right uu____1505
                         FStar_Interactive_JsonHelper.js_str in
                     (uu____1494, uu____1504) in
                   VfsAdd uu____1487
               | uu____1508 ->
                   let uu____1509 =
                     FStar_Util.format1 "Unknown query '%s'" query1 in
                   ProtocolViolation uu____1509 in
             { qq = uu____1355; qid }) ()
    with
    | FStar_Interactive_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure qid expected got
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query ->
    try
      (fun uu___294_1522 ->
         match () with | () -> unpack_interactive_query js_query) ()
    with
    | FStar_Interactive_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid = "?" }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure "?" expected got
let (parse_interactive_query : Prims.string -> query) =
  fun query_str ->
    let uu____1534 = FStar_Util.json_of_string query_str in
    match uu____1534 with
    | FStar_Pervasives_Native.None ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream ->
    let uu____1543 = FStar_Util.read_line stream in
    match uu____1543 with
    | FStar_Pervasives_Native.None -> FStar_All.exit Prims.int_zero
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
let json_of_opt :
  'uuuuuu1553 .
    ('uuuuuu1553 -> FStar_Util.json) ->
      'uuuuuu1553 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a ->
    fun opt_a ->
      let uu____1573 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____1573
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
    let uu____1586 =
      let uu____1593 =
        let uu____1600 =
          let uu____1607 =
            let uu____1614 =
              let uu____1619 =
                let uu____1620 =
                  let uu____1623 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.None -> []
                    | FStar_Pervasives_Native.Some r ->
                        let uu____1629 = FStar_Range.json_of_use_range r in
                        [uu____1629] in
                  let uu____1630 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.Some r when
                        let uu____1636 = FStar_Range.def_range r in
                        let uu____1637 = FStar_Range.use_range r in
                        uu____1636 <> uu____1637 ->
                        let uu____1638 = FStar_Range.json_of_def_range r in
                        [uu____1638]
                    | uu____1639 -> [] in
                  FStar_List.append uu____1623 uu____1630 in
                FStar_Util.JsonList uu____1620 in
              ("ranges", uu____1619) in
            [uu____1614] in
          ("message",
            (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))) ::
            uu____1607 in
        FStar_List.append
          (match issue.FStar_Errors.issue_number with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some n ->
               [("number", (FStar_Util.JsonInt n))]) uu____1600 in
      FStar_List.append
        [("level", (json_of_issue_level issue.FStar_Errors.issue_level))]
        uu____1593 in
    FStar_All.pipe_left (fun uu____1695 -> FStar_Util.JsonAssoc uu____1695)
      uu____1586
let (alist_of_symbol_lookup_result :
  FStar_Interactive_QueryHelper.sl_reponse ->
    (Prims.string * FStar_Util.json) Prims.list)
  =
  fun lr ->
    let uu____1707 =
      let uu____1714 =
        let uu____1719 =
          json_of_opt FStar_Range.json_of_def_range
            lr.FStar_Interactive_QueryHelper.slr_def_range in
        ("defined-at", uu____1719) in
      let uu____1720 =
        let uu____1727 =
          let uu____1732 =
            json_of_opt (fun uu____1733 -> FStar_Util.JsonStr uu____1733)
              lr.FStar_Interactive_QueryHelper.slr_typ in
          ("type", uu____1732) in
        let uu____1734 =
          let uu____1741 =
            let uu____1746 =
              json_of_opt (fun uu____1747 -> FStar_Util.JsonStr uu____1747)
                lr.FStar_Interactive_QueryHelper.slr_doc in
            ("documentation", uu____1746) in
          let uu____1748 =
            let uu____1755 =
              let uu____1760 =
                json_of_opt (fun uu____1761 -> FStar_Util.JsonStr uu____1761)
                  lr.FStar_Interactive_QueryHelper.slr_def in
              ("definition", uu____1760) in
            [uu____1755] in
          uu____1741 :: uu____1748 in
        uu____1727 :: uu____1734 in
      uu____1714 :: uu____1720 in
    ("name",
      (FStar_Util.JsonStr (lr.FStar_Interactive_QueryHelper.slr_name))) ::
      uu____1707
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____1794 =
      FStar_List.map (fun uu____1797 -> FStar_Util.JsonStr uu____1797)
        interactive_protocol_features in
    FStar_All.pipe_left (fun uu____1800 -> FStar_Util.JsonList uu____1800)
      uu____1794 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptSet -> true | uu____1818 -> false
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReadOnly -> true | uu____1824 -> false
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___3_1829 ->
    match uu___3_1829 with | OptSet -> "" | OptReadOnly -> "read-only"
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
  fun uu___4_2022 ->
    match uu___4_2022 with
    | FStar_Options.Const uu____2023 -> "flag"
    | FStar_Options.IntStr uu____2024 -> "int"
    | FStar_Options.BoolStr -> "bool"
    | FStar_Options.PathStr uu____2025 -> "path"
    | FStar_Options.SimpleStr uu____2026 -> "string"
    | FStar_Options.EnumStr uu____2027 -> "enum"
    | FStar_Options.OpenEnumStr uu____2030 -> "open enum"
    | FStar_Options.PostProcessed (uu____2037, typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____2047, typ) ->
        kind_of_fstar_option_type typ
let (snippets_of_fstar_option :
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
        | FStar_Options.Const uu____2095 -> [""]
        | FStar_Options.BoolStr -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs, desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____2108, elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____2118, elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____2126 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____2126
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___5_2133 ->
    match uu___5_2133 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n -> FStar_Util.JsonInt n
    | FStar_Options.List vs ->
        let uu____2141 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____2141
    | FStar_Options.Unset -> FStar_Util.JsonNull
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt ->
    let uu____2155 =
      let uu____2162 =
        let uu____2169 =
          let uu____2174 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____2174) in
        let uu____2175 =
          let uu____2182 =
            let uu____2187 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____2187) in
          let uu____2188 =
            let uu____2195 =
              let uu____2200 =
                json_of_opt (fun uu____2201 -> FStar_Util.JsonStr uu____2201)
                  opt.opt_documentation in
              ("documentation", uu____2200) in
            let uu____2202 =
              let uu____2209 =
                let uu____2214 =
                  let uu____2215 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____2215 in
                ("type", uu____2214) in
              [uu____2209;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____2195 :: uu____2202 in
          uu____2182 :: uu____2188 in
        uu____2169 :: uu____2175 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____2162 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____2155
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt ->
    let uu____2253 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____2253
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
        FStar_Interactive_JsonHelper.write_json
          (json_of_response qid status response)
let (json_of_message : Prims.string -> FStar_Util.json -> FStar_Util.json) =
  fun level ->
    fun js_contents ->
      let uu____2322 =
        let uu____2329 =
          let uu____2336 =
            let uu____2341 =
              let uu____2342 = FStar_ST.op_Bang repl_current_qid in
              json_of_opt (fun uu____2355 -> FStar_Util.JsonStr uu____2355)
                uu____2342 in
            ("query-id", uu____2341) in
          [uu____2336;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)] in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____2329 in
      FStar_Util.JsonAssoc uu____2322
let forward_message :
  'uuuuuu2384 .
    (FStar_Util.json -> 'uuuuuu2384) ->
      Prims.string -> FStar_Util.json -> 'uuuuuu2384
  =
  fun callback ->
    fun level ->
      fun contents ->
        let uu____2405 = json_of_message level contents in
        callback uu____2405
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____2408 =
      FStar_List.map (fun uu____2411 -> FStar_Util.JsonStr uu____2411)
        interactive_protocol_features in
    FStar_Util.JsonList uu____2408 in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
let (write_hello : unit -> unit) =
  fun uu____2420 -> FStar_Interactive_JsonHelper.write_json json_of_hello
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name ->
    fun typ ->
      let flag = Prims.op_Hat "--" name in
      let uu____2432 = FStar_Options.desc_of_opt_type typ in
      match uu____2432 with
      | FStar_Pervasives_Native.None -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____2441 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____2470 ->
            match uu____2470 with
            | (_shortname, name, typ, doc) ->
                let uu____2485 = FStar_Util.smap_try_find defaults name in
                FStar_All.pipe_right uu____2485
                  (FStar_Util.map_option
                     (fun default_value ->
                        let uu____2497 = sig_of_fstar_option name typ in
                        let uu____2498 = snippets_of_fstar_option name typ in
                        let uu____2501 =
                          let uu____2502 = FStar_Options.settable name in
                          if uu____2502 then OptSet else OptReadOnly in
                        {
                          opt_name = name;
                          opt_sig = uu____2497;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____2498;
                          opt_documentation =
                            (if doc = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc);
                          opt_permission_level = uu____2501
                        })))) in
  FStar_All.pipe_right uu____2441
    (FStar_List.sortWith
       (fun o1 ->
          fun o2 ->
            FStar_String.compare (FStar_String.lowercase o1.opt_name)
              (FStar_String.lowercase o2.opt_name)))
let (fstar_options_map_cache : fstar_option FStar_Util.smap) =
  let cache = FStar_Util.smap_create (Prims.of_int (50)) in
  FStar_List.iter (fun opt -> FStar_Util.smap_add cache opt.opt_name opt)
    fstar_options_list_cache;
  cache
let (update_option : fstar_option -> fstar_option) =
  fun opt ->
    let uu___467_2528 = opt in
    let uu____2529 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___467_2528.opt_name);
      opt_sig = (uu___467_2528.opt_sig);
      opt_value = uu____2529;
      opt_default = (uu___467_2528.opt_default);
      opt_type = (uu___467_2528.opt_type);
      opt_snippets = (uu___467_2528.opt_snippets);
      opt_documentation = (uu___467_2528.opt_documentation);
      opt_permission_level = (uu___467_2528.opt_permission_level)
    }
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter ->
    let uu____2542 = FStar_List.filter filter fstar_options_list_cache in
    FStar_List.map update_option uu____2542
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____2559 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____2559)
    else ("", opt_name)
let (json_of_repl_state :
  FStar_Interactive_JsonHelper.repl_state -> FStar_Util.json) =
  fun st ->
    let filenames uu____2581 =
      match uu____2581 with
      | (uu____2592, (task, uu____2594)) ->
          (match task with
           | FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) ->
               [intf.FStar_Interactive_JsonHelper.tf_fname;
               impl.FStar_Interactive_JsonHelper.tf_fname]
           | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
               [intf_or_impl.FStar_Interactive_JsonHelper.tf_fname]
           | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
               [intf.FStar_Interactive_JsonHelper.tf_fname]
           | uu____2605 -> []) in
    let uu____2606 =
      let uu____2613 =
        let uu____2618 =
          let uu____2619 =
            let uu____2622 =
              FStar_List.concatMap filenames
                st.FStar_Interactive_JsonHelper.repl_deps_stack in
            FStar_List.map (fun uu____2633 -> FStar_Util.JsonStr uu____2633)
              uu____2622 in
          FStar_Util.JsonList uu____2619 in
        ("loaded-dependencies", uu____2618) in
      let uu____2634 =
        let uu____2641 =
          let uu____2646 =
            let uu____2647 =
              let uu____2650 = current_fstar_options (fun uu____2655 -> true) in
              FStar_List.map json_of_fstar_option uu____2650 in
            FStar_Util.JsonList uu____2647 in
          ("options", uu____2646) in
        [uu____2641] in
      uu____2613 :: uu____2634 in
    FStar_Util.JsonAssoc uu____2606
let run_exit :
  'uuuuuu2674 'uuuuuu2675 .
    'uuuuuu2674 ->
      ((query_status * FStar_Util.json) * ('uuuuuu2675, Prims.int)
        FStar_Util.either)
  =
  fun st -> ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr Prims.int_zero))
let run_describe_protocol :
  'uuuuuu2707 'uuuuuu2708 .
    'uuuuuu2707 ->
      ((query_status * FStar_Util.json) * ('uuuuuu2707, 'uuuuuu2708)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl :
  'uuuuuu2738 .
    FStar_Interactive_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu2738)
        FStar_Util.either)
  =
  fun st ->
    let uu____2756 =
      let uu____2761 = json_of_repl_state st in (QueryOK, uu____2761) in
    (uu____2756, (FStar_Util.Inl st))
let run_protocol_violation :
  'uuuuuu2778 'uuuuuu2779 .
    'uuuuuu2778 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('uuuuuu2778, 'uuuuuu2779)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error :
  'uuuuuu2818 'uuuuuu2819 .
    'uuuuuu2818 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('uuuuuu2818, 'uuuuuu2819)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____2856 ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_segment :
  'uuuuuu2867 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu2867)
          FStar_Util.either)
  =
  fun st ->
    fun code ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_fname = "<input>";
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = Prims.int_one;
          FStar_Parser_ParseIt.frag_col = Prims.int_zero
        } in
      let collect_decls uu____2898 =
        let uu____2899 = FStar_Parser_Driver.parse_fragment frag in
        match uu____2899 with
        | FStar_Parser_Driver.Empty -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____2905, decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____2911, decls, uu____2913)) -> decls in
      let uu____2918 =
        with_captured_errors st.FStar_Interactive_JsonHelper.repl_env
          FStar_Util.sigint_ignore
          (fun uu____2927 ->
             let uu____2928 = collect_decls () in
             FStar_All.pipe_left
               (fun uu____2939 -> FStar_Pervasives_Native.Some uu____2939)
               uu____2928) in
      match uu____2918 with
      | FStar_Pervasives_Native.None ->
          let errors =
            let uu____2957 = collect_errors () in
            FStar_All.pipe_right uu____2957 (FStar_List.map json_of_issue) in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____2983 =
              let uu____2990 =
                let uu____2995 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl) in
                ("def_range", uu____2995) in
              [uu____2990] in
            FStar_Util.JsonAssoc uu____2983 in
          let js_decls =
            let uu____3005 = FStar_List.map json_of_decl decls in
            FStar_All.pipe_left
              (fun uu____3010 -> FStar_Util.JsonList uu____3010) uu____3005 in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
let run_vfs_add :
  'uuuuuu3035 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu3035)
            FStar_Util.either)
  =
  fun st ->
    fun opt_fname ->
      fun contents ->
        let fname =
          FStar_Util.dflt st.FStar_Interactive_JsonHelper.repl_fname
            opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop :
  'uuuuuu3081 .
    FStar_Interactive_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu3081)
        FStar_Util.either)
  =
  fun st ->
    let uu____3099 = nothing_left_to_pop st in
    if uu____3099
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let st' = FStar_Interactive_PushHelper.pop_repl "pop_query" st in
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
      let uu____3169 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents) in
      FStar_Interactive_JsonHelper.write_json uu____3169
let (write_repl_ld_task_progress :
  FStar_Interactive_JsonHelper.repl_task -> unit) =
  fun task ->
    match task with
    | FStar_Interactive_JsonHelper.LDInterleaved (uu____3175, tf) ->
        let modname =
          FStar_Parser_Dep.module_name_of_file
            tf.FStar_Interactive_JsonHelper.tf_fname in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | FStar_Interactive_JsonHelper.LDSingle tf ->
        let modname =
          FStar_Parser_Dep.module_name_of_file
            tf.FStar_Interactive_JsonHelper.tf_fname in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile tf ->
        let modname =
          FStar_Parser_Dep.module_name_of_file
            tf.FStar_Interactive_JsonHelper.tf_fname in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | uu____3206 -> ()
let (load_deps :
  FStar_Interactive_JsonHelper.repl_state ->
    ((FStar_Interactive_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_Interactive_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st ->
    let uu____3222 =
      with_captured_errors st.FStar_Interactive_JsonHelper.repl_env
        FStar_Util.sigint_ignore
        (fun _env ->
           let uu____3248 =
             FStar_Interactive_PushHelper.deps_and_repl_ld_tasks_of_our_file
               st.FStar_Interactive_JsonHelper.repl_fname in
           FStar_All.pipe_left
             (fun uu____3291 -> FStar_Pervasives_Native.Some uu____3291)
             uu____3248) in
    match uu____3222 with
    | FStar_Pervasives_Native.None -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps, tasks, dep_graph) ->
        let st1 =
          let uu___557_3340 = st in
          let uu____3341 =
            FStar_TypeChecker_Env.set_dep_graph
              st.FStar_Interactive_JsonHelper.repl_env dep_graph in
          {
            FStar_Interactive_JsonHelper.repl_line =
              (uu___557_3340.FStar_Interactive_JsonHelper.repl_line);
            FStar_Interactive_JsonHelper.repl_column =
              (uu___557_3340.FStar_Interactive_JsonHelper.repl_column);
            FStar_Interactive_JsonHelper.repl_fname =
              (uu___557_3340.FStar_Interactive_JsonHelper.repl_fname);
            FStar_Interactive_JsonHelper.repl_deps_stack =
              (uu___557_3340.FStar_Interactive_JsonHelper.repl_deps_stack);
            FStar_Interactive_JsonHelper.repl_curmod =
              (uu___557_3340.FStar_Interactive_JsonHelper.repl_curmod);
            FStar_Interactive_JsonHelper.repl_env = uu____3341;
            FStar_Interactive_JsonHelper.repl_stdin =
              (uu___557_3340.FStar_Interactive_JsonHelper.repl_stdin);
            FStar_Interactive_JsonHelper.repl_names =
              (uu___557_3340.FStar_Interactive_JsonHelper.repl_names)
          } in
        let uu____3342 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress in
        (match uu____3342 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue ->
    let uu___567_3388 = issue in
    let uu____3389 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____3389;
      FStar_Errors.issue_level = (uu___567_3388.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___567_3388.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___567_3388.FStar_Errors.issue_number)
    }
let run_push_without_deps :
  'uuuuuu3396 .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu3396)
          FStar_Util.either)
  =
  fun st ->
    fun query1 ->
      let set_nosynth_flag st1 flag =
        let uu___574_3430 = st1 in
        {
          FStar_Interactive_JsonHelper.repl_line =
            (uu___574_3430.FStar_Interactive_JsonHelper.repl_line);
          FStar_Interactive_JsonHelper.repl_column =
            (uu___574_3430.FStar_Interactive_JsonHelper.repl_column);
          FStar_Interactive_JsonHelper.repl_fname =
            (uu___574_3430.FStar_Interactive_JsonHelper.repl_fname);
          FStar_Interactive_JsonHelper.repl_deps_stack =
            (uu___574_3430.FStar_Interactive_JsonHelper.repl_deps_stack);
          FStar_Interactive_JsonHelper.repl_curmod =
            (uu___574_3430.FStar_Interactive_JsonHelper.repl_curmod);
          FStar_Interactive_JsonHelper.repl_env =
            (let uu___576_3432 = st1.FStar_Interactive_JsonHelper.repl_env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___576_3432.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___576_3432.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___576_3432.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___576_3432.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___576_3432.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___576_3432.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___576_3432.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___576_3432.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___576_3432.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___576_3432.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___576_3432.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___576_3432.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___576_3432.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___576_3432.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___576_3432.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___576_3432.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___576_3432.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___576_3432.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___576_3432.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___576_3432.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___576_3432.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___576_3432.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___576_3432.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___576_3432.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___576_3432.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___576_3432.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___576_3432.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___576_3432.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___576_3432.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___576_3432.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___576_3432.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___576_3432.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___576_3432.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___576_3432.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___576_3432.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___576_3432.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___576_3432.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___576_3432.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___576_3432.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___576_3432.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___576_3432.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___576_3432.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___576_3432.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___576_3432.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___576_3432.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (uu___576_3432.FStar_TypeChecker_Env.enable_defer_to_tac)
             });
          FStar_Interactive_JsonHelper.repl_stdin =
            (uu___574_3430.FStar_Interactive_JsonHelper.repl_stdin);
          FStar_Interactive_JsonHelper.repl_names =
            (uu___574_3430.FStar_Interactive_JsonHelper.repl_names)
        } in
      let uu____3433 = query1 in
      match uu____3433 with
      | { push_kind; push_code = text; push_line = line;
          push_column = column; push_peek_only = peek_only;_} ->
          let frag =
            {
              FStar_Parser_ParseIt.frag_fname = "<input>";
              FStar_Parser_ParseIt.frag_text = text;
              FStar_Parser_ParseIt.frag_line = line;
              FStar_Parser_ParseIt.frag_col = column
            } in
          (FStar_TypeChecker_Env.toggle_id_info
             st.FStar_Interactive_JsonHelper.repl_env true;
           (let st1 = set_nosynth_flag st peek_only in
            let uu____3454 =
              run_repl_transaction st1 push_kind peek_only
                (FStar_Interactive_JsonHelper.PushFragment frag) in
            match uu____3454 with
            | (success, st2) ->
                let st3 = set_nosynth_flag st2 false in
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu____3477 =
                    let uu____3480 = collect_errors () in
                    FStar_All.pipe_right uu____3480
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu____3477 in
                let st4 =
                  if success
                  then
                    let uu___595_3488 = st3 in
                    {
                      FStar_Interactive_JsonHelper.repl_line = line;
                      FStar_Interactive_JsonHelper.repl_column = column;
                      FStar_Interactive_JsonHelper.repl_fname =
                        (uu___595_3488.FStar_Interactive_JsonHelper.repl_fname);
                      FStar_Interactive_JsonHelper.repl_deps_stack =
                        (uu___595_3488.FStar_Interactive_JsonHelper.repl_deps_stack);
                      FStar_Interactive_JsonHelper.repl_curmod =
                        (uu___595_3488.FStar_Interactive_JsonHelper.repl_curmod);
                      FStar_Interactive_JsonHelper.repl_env =
                        (uu___595_3488.FStar_Interactive_JsonHelper.repl_env);
                      FStar_Interactive_JsonHelper.repl_stdin =
                        (uu___595_3488.FStar_Interactive_JsonHelper.repl_stdin);
                      FStar_Interactive_JsonHelper.repl_names =
                        (uu___595_3488.FStar_Interactive_JsonHelper.repl_names)
                    }
                  else st3 in
                ((status, json_errors), (FStar_Util.Inl st4))))
let run_push_with_deps :
  'uuuuuu3504 .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu3504)
          FStar_Util.either)
  =
  fun st ->
    fun query1 ->
      (let uu____3528 = FStar_Options.debug_any () in
       if uu____3528
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info
        st.FStar_Interactive_JsonHelper.repl_env false;
      (let uu____3531 = load_deps st in
       match uu____3531 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____3564 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu____3564 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1, deps) ->
           ((let uu____3595 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____3595 (fun uu____3596 -> ()));
            (let names =
               FStar_Interactive_PushHelper.add_module_completions
                 st1.FStar_Interactive_JsonHelper.repl_fname deps
                 st1.FStar_Interactive_JsonHelper.repl_names in
             run_push_without_deps
               (let uu___613_3599 = st1 in
                {
                  FStar_Interactive_JsonHelper.repl_line =
                    (uu___613_3599.FStar_Interactive_JsonHelper.repl_line);
                  FStar_Interactive_JsonHelper.repl_column =
                    (uu___613_3599.FStar_Interactive_JsonHelper.repl_column);
                  FStar_Interactive_JsonHelper.repl_fname =
                    (uu___613_3599.FStar_Interactive_JsonHelper.repl_fname);
                  FStar_Interactive_JsonHelper.repl_deps_stack =
                    (uu___613_3599.FStar_Interactive_JsonHelper.repl_deps_stack);
                  FStar_Interactive_JsonHelper.repl_curmod =
                    (uu___613_3599.FStar_Interactive_JsonHelper.repl_curmod);
                  FStar_Interactive_JsonHelper.repl_env =
                    (uu___613_3599.FStar_Interactive_JsonHelper.repl_env);
                  FStar_Interactive_JsonHelper.repl_stdin =
                    (uu___613_3599.FStar_Interactive_JsonHelper.repl_stdin);
                  FStar_Interactive_JsonHelper.repl_names = names
                }) query1)))
let run_push :
  'uuuuuu3606 .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu3606)
          FStar_Util.either)
  =
  fun st ->
    fun query1 ->
      let uu____3629 = nothing_left_to_pop st in
      if uu____3629
      then run_push_with_deps st query1
      else run_push_without_deps st query1
let (run_symbol_lookup :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      FStar_Interactive_QueryHelper.position FStar_Pervasives_Native.option
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
          let uu____3685 =
            FStar_Interactive_QueryHelper.symlookup
              st.FStar_Interactive_JsonHelper.repl_env symbol pos_opt
              requested_info in
          match uu____3685 with
          | FStar_Pervasives_Native.None -> FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some result ->
              let uu____3713 =
                let uu____3724 = alist_of_symbol_lookup_result result in
                ("symbol", uu____3724) in
              FStar_Util.Inr uu____3713
let (run_option_lookup :
  Prims.string ->
    (Prims.string,
      (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
      FStar_Util.either)
  =
  fun opt_name ->
    let uu____3766 = trim_option_name opt_name in
    match uu____3766 with
    | (uu____3785, trimmed_name) ->
        let uu____3787 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____3787 with
         | FStar_Pervasives_Native.None ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____3815 =
               let uu____3826 =
                 let uu____3833 = update_option opt in
                 alist_of_fstar_option uu____3833 in
               ("option", uu____3826) in
             FStar_Util.Inr uu____3815)
let (run_module_lookup :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string,
        (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
        FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      let query1 = FStar_Util.split symbol "." in
      let uu____3877 =
        FStar_Interactive_CompletionTable.find_module_or_ns
          st.FStar_Interactive_JsonHelper.repl_names query1 in
      match uu____3877 with
      | FStar_Pervasives_Native.None ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____3905 =
            let uu____3916 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____3916) in
          FStar_Util.Inr uu____3905
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____3940 =
            let uu____3951 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____3951) in
          FStar_Util.Inr uu____3940
let (run_code_lookup :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      FStar_Interactive_QueryHelper.position FStar_Pervasives_Native.option
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
          let uu____4016 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____4016 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____4076 ->
              let uu____4087 = run_module_lookup st symbol in
              (match uu____4087 with
               | FStar_Util.Inr alist -> FStar_Util.Inr alist
               | FStar_Util.Inl err_msg ->
                   FStar_Util.Inl "No such symbol, module, or namespace.")
let (run_lookup' :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      lookup_context ->
        FStar_Interactive_QueryHelper.position FStar_Pervasives_Native.option
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
  'uuuuuu4241 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        lookup_context ->
          FStar_Interactive_QueryHelper.position
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) *
                (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu4241)
                FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun context ->
        fun pos_opt ->
          fun requested_info ->
            let uu____4287 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____4287 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind, info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let run_code_autocomplete :
  'uuuuuu4375 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu4375)
          FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      let result = FStar_Interactive_QueryHelper.ck_completion st search_term in
      let js =
        FStar_List.map
          FStar_Interactive_CompletionTable.json_of_completion_result result in
      ((QueryOK, (FStar_Util.JsonList js)), (FStar_Util.Inl st))
let run_module_autocomplete :
  'uuuuuu4426 'uuuuuu4427 'uuuuuu4428 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        'uuuuuu4426 ->
          'uuuuuu4427 ->
            ((query_status * FStar_Util.json) *
              (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu4428)
              FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun modules ->
        fun namespaces ->
          let needle = FStar_Util.split search_term "." in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.FStar_Interactive_JsonHelper.repl_names needle
              (fun uu____4471 -> FStar_Pervasives_Native.Some uu____4471) in
          let json =
            FStar_List.map
              FStar_Interactive_CompletionTable.json_of_completion_result
              mods_and_nss in
          ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let candidates_of_fstar_option :
  'uuuuuu4491 .
    Prims.int ->
      'uuuuuu4491 ->
        fstar_option ->
          FStar_Interactive_CompletionTable.completion_result Prims.list
  =
  fun match_len ->
    fun is_reset ->
      fun opt ->
        let uu____4509 =
          match opt.opt_permission_level with
          | OptSet -> (true, "")
          | OptReadOnly -> (false, "read-only") in
        match uu____4509 with
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
  'uuuuuu4543 'uuuuuu4544 'uuuuuu4545 .
    'uuuuuu4543 ->
      Prims.string ->
        'uuuuuu4544 ->
          ((query_status * FStar_Util.json) * ('uuuuuu4543, 'uuuuuu4545)
            FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun is_reset ->
        let uu____4573 = trim_option_name search_term in
        match uu____4573 with
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
        | (uu____4622, uu____4623) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete :
  'uuuuuu4640 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu4640)
            FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun context ->
        match context with
        | CKCode -> run_code_autocomplete st search_term
        | CKOption is_reset ->
            run_option_autocomplete st search_term is_reset
        | CKModuleOrNamespace (modules, namespaces) ->
            run_module_autocomplete st search_term modules namespaces
let run_and_rewind :
  'uuuuuu4681 'uuuuuu4682 .
    FStar_Interactive_JsonHelper.repl_state ->
      'uuuuuu4681 ->
        (FStar_Interactive_JsonHelper.repl_state -> 'uuuuuu4681) ->
          ('uuuuuu4681 * (FStar_Interactive_JsonHelper.repl_state,
            'uuuuuu4682) FStar_Util.either)
  =
  fun st ->
    fun sigint_default ->
      fun task ->
        let st1 =
          FStar_Interactive_PushHelper.push_repl "run_and_rewind"
            FStar_Interactive_PushHelper.FullCheck
            FStar_Interactive_JsonHelper.Noop st in
        let results =
          try
            (fun uu___728_4722 ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____4733 ->
                        let uu____4734 = task st1 in
                        FStar_All.pipe_left
                          (fun uu____4739 -> FStar_Util.Inl uu____4739)
                          uu____4734)) ()
          with | FStar_Util.SigInt -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e in
        let st2 = FStar_Interactive_PushHelper.pop_repl "run_and_rewind" st1 in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
let run_with_parsed_and_tc_term :
  'uuuuuu4786 'uuuuuu4787 'uuuuuu4788 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        'uuuuuu4786 ->
          'uuuuuu4787 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) *
                (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu4788)
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
                FStar_Parser_ParseIt.frag_fname = "<input>";
                FStar_Parser_ParseIt.frag_text = dummy_decl;
                FStar_Parser_ParseIt.frag_line = Prims.int_zero;
                FStar_Parser_ParseIt.frag_col = Prims.int_zero
              } in
            let find_let_body ses =
              match ses with
              | {
                  FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                    ((uu____4881,
                      { FStar_Syntax_Syntax.lbname = uu____4882;
                        FStar_Syntax_Syntax.lbunivs = univs;
                        FStar_Syntax_Syntax.lbtyp = uu____4884;
                        FStar_Syntax_Syntax.lbeff = uu____4885;
                        FStar_Syntax_Syntax.lbdef = def;
                        FStar_Syntax_Syntax.lbattrs = uu____4887;
                        FStar_Syntax_Syntax.lbpos = uu____4888;_}::[]),
                     uu____4889);
                  FStar_Syntax_Syntax.sigrng = uu____4890;
                  FStar_Syntax_Syntax.sigquals = uu____4891;
                  FStar_Syntax_Syntax.sigmeta = uu____4892;
                  FStar_Syntax_Syntax.sigattrs = uu____4893;
                  FStar_Syntax_Syntax.sigopts = uu____4894;_}::[] ->
                  FStar_Pervasives_Native.Some (univs, def)
              | uu____4933 -> FStar_Pervasives_Native.None in
            let parse frag =
              let uu____4954 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag) in
              match uu____4954 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls, uu____4960) ->
                  FStar_Pervasives_Native.Some decls
              | uu____4979 -> FStar_Pervasives_Native.None in
            let desugar env decls =
              let uu____4997 =
                let uu____5002 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
                uu____5002 env.FStar_TypeChecker_Env.dsenv in
              FStar_Pervasives_Native.fst uu____4997 in
            let typecheck tcenv decls =
              let uu____5024 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
              match uu____5024 with | (ses, uu____5034) -> ses in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1 ->
                 let tcenv = st1.FStar_Interactive_JsonHelper.repl_env in
                 let frag = dummy_let_fragment term in
                 let uu____5050 = parse frag in
                 match uu____5050 with
                 | FStar_Pervasives_Native.None ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____5075 =
                       let decls1 = desugar tcenv decls in
                       let ses = typecheck tcenv decls1 in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs, def) ->
                           let uu____5110 =
                             FStar_Syntax_Subst.open_univ_vars univs def in
                           (match uu____5110 with
                            | (univs1, def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs1 in
                                continuation tcenv1 def1) in
                     let uu____5122 = FStar_Options.trace_error () in
                     if uu____5122
                     then aux ()
                     else
                       (try
                          (fun uu___811_5133 -> match () with | () -> aux ())
                            ()
                        with
                        | uu___810_5142 ->
                            let uu____5147 =
                              FStar_Errors.issue_of_exn uu___810_5142 in
                            (match uu____5147 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____5155 =
                                   let uu____5156 =
                                     FStar_Errors.format_issue issue in
                                   FStar_Util.JsonStr uu____5156 in
                                 (QueryNOK, uu____5155)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Exn.raise uu___810_5142)))
let run_compute :
  'uuuuuu5169 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu5169)
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
        let normalize_term tcenv rules2 t =
          FStar_TypeChecker_Normalize.normalize rules2 tcenv t in
        run_with_parsed_and_tc_term st term Prims.int_zero Prims.int_zero
          (fun tcenv ->
             fun def ->
               let normalized = normalize_term tcenv rules1 def in
               let uu____5241 =
                 let uu____5242 =
                   FStar_Interactive_QueryHelper.term_to_string tcenv
                     normalized in
                 FStar_Util.JsonStr uu____5242 in
               (QueryOK, uu____5241))
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NameContainsStr _0 -> true | uu____5269 -> false
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee -> match projectee with | NameContainsStr _0 -> _0
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeContainsLid _0 -> true | uu____5282 -> false
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TypeContainsLid _0 -> _0
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | { st_negate; st_term;_} -> st_negate
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee -> match projectee with | { st_negate; st_term;_} -> st_term
let (st_cost : search_term' -> Prims.int) =
  fun uu___6_5307 ->
    match uu___6_5307 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> Prims.int_one
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
    let uu____5418 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____5425 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____5418; sc_fvars = uu____5425 }
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv ->
    fun sc ->
      let uu____5448 = FStar_ST.op_Bang sc.sc_typ in
      match uu____5448 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let typ =
            let uu____5463 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____5463 with
            | FStar_Pervasives_Native.None ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____5482, typ), uu____5484) ->
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
      let uu____5520 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____5520 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None ->
          let fv =
            let uu____5551 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____5551 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv ->
    fun sc ->
      let typ_str =
        let uu____5580 = sc_typ tcenv sc in
        FStar_Interactive_QueryHelper.term_to_string tcenv uu____5580 in
      let uu____5581 =
        let uu____5588 =
          let uu____5593 =
            let uu____5594 =
              let uu____5595 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              FStar_Ident.string_of_lid uu____5595 in
            FStar_Util.JsonStr uu____5594 in
          ("lid", uu____5593) in
        [uu____5588; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu____5581
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidSearch uu____5617 -> true
    | uu____5618 -> false
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidSearch uu____5624 -> uu____5624
let run_search :
  'uuuuuu5631 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuuu5631)
          FStar_Util.either)
  =
  fun st ->
    fun search_str ->
      let tcenv = st.FStar_Interactive_JsonHelper.repl_env in
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              let uu____5671 = FStar_Ident.string_of_lid candidate.sc_lid in
              FStar_Util.contains uu____5671 str
          | TypeContainsLid lid ->
              let uu____5673 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____5673 in
        found <> term.st_negate in
      let parse search_str1 =
        let parse_one term =
          let negate = FStar_Util.starts_with term "-" in
          let term1 =
            if negate
            then FStar_Util.substring_from term Prims.int_one
            else term in
          let beg_quote = FStar_Util.starts_with term1 "\"" in
          let end_quote = FStar_Util.ends_with term1 "\"" in
          let strip_quotes str =
            if (FStar_String.length str) < (Prims.of_int (2))
            then FStar_Exn.raise (InvalidSearch "Empty search term")
            else
              FStar_Util.substring str Prims.int_one
                ((FStar_String.length term1) - (Prims.of_int (2))) in
          let parsed =
            if beg_quote <> end_quote
            then
              let uu____5703 =
                let uu____5704 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____5704 in
              FStar_Exn.raise uu____5703
            else
              if beg_quote
              then
                (let uu____5706 = strip_quotes term1 in
                 NameContainsStr uu____5706)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____5709 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu____5709 with
                 | FStar_Pervasives_Native.None ->
                     let uu____5712 =
                       let uu____5713 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____5713 in
                     FStar_Exn.raise uu____5712
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____5735 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l ->
              let uu____5738 = FStar_Ident.string_of_lid l in
              FStar_Util.format1 "%s" uu____5738 in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____5735 in
      let results =
        try
          (fun uu___924_5760 ->
             match () with
             | () ->
                 let terms = parse search_str in
                 let all_lidents = FStar_TypeChecker_Env.lidents tcenv in
                 let all_candidates = FStar_List.map sc_of_lid all_lidents in
                 let matches_all candidate =
                   FStar_List.for_all (st_matches candidate) terms in
                 let cmp r1 r2 =
                   let uu____5791 = FStar_Ident.string_of_lid r1.sc_lid in
                   let uu____5792 = FStar_Ident.string_of_lid r2.sc_lid in
                   FStar_Util.compare uu____5791 uu____5792 in
                 let results = FStar_List.filter matches_all all_candidates in
                 let sorted = FStar_Util.sort_with cmp results in
                 let js = FStar_List.map (json_of_search_result tcenv) sorted in
                 (match results with
                  | [] ->
                      let kwds =
                        let uu____5807 = FStar_List.map pprint_one terms in
                        FStar_Util.concat_l " " uu____5807 in
                      let uu____5810 =
                        let uu____5811 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds in
                        InvalidSearch uu____5811 in
                      FStar_Exn.raise uu____5810
                  | uu____5816 -> (QueryOK, (FStar_Util.JsonList js)))) ()
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
      (results, (FStar_Util.Inl st))
let (run_query :
  FStar_Interactive_JsonHelper.repl_state ->
    query' ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun q ->
      match q with
      | Exit -> run_exit st
      | DescribeProtocol -> run_describe_protocol st
      | DescribeRepl -> run_describe_repl st
      | GenericError message -> run_generic_error st message
      | ProtocolViolation query1 -> run_protocol_violation st query1
      | Segment c -> run_segment st c
      | VfsAdd (fname, contents) -> run_vfs_add st fname contents
      | Push pquery -> run_push st pquery
      | Pop -> run_pop st
      | AutoComplete (search_term1, context) ->
          run_autocomplete st search_term1 context
      | Lookup (symbol, context, pos_opt, rq_info) ->
          run_lookup st symbol context pos_opt rq_info
      | Compute (term, rules) -> run_compute st term rules
      | Search term -> run_search st term
let (validate_query :
  FStar_Interactive_JsonHelper.repl_state -> query -> query) =
  fun st ->
    fun q ->
      match q.qq with
      | Push
          { push_kind = FStar_Interactive_PushHelper.SyntaxCheck;
            push_code = uu____5914; push_line = uu____5915;
            push_column = uu____5916; push_peek_only = false;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____5917 ->
          (match st.FStar_Interactive_JsonHelper.repl_curmod with
           | FStar_Pervasives_Native.None when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____5918 -> q)
let (validate_and_run_query :
  FStar_Interactive_JsonHelper.repl_state ->
    query ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query1 ->
      let query2 = validate_query st query1 in
      FStar_ST.op_Colon_Equals repl_current_qid
        (FStar_Pervasives_Native.Some (query2.qid));
      run_query st query2.qq
let (js_repl_eval :
  FStar_Interactive_JsonHelper.repl_state ->
    query ->
      (FStar_Util.json * (FStar_Interactive_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query1 ->
      let uu____5971 = validate_and_run_query st query1 in
      match uu____5971 with
      | ((status, response), st_opt) ->
          let js_response = json_of_response query1.qid status response in
          (js_response, st_opt)
let (js_repl_eval_js :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Util.json ->
      (FStar_Util.json * (FStar_Interactive_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query_js ->
      let uu____6030 = deserialize_interactive_query query_js in
      js_repl_eval st uu____6030
let (js_repl_eval_str :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string * (FStar_Interactive_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query_str ->
      let uu____6049 =
        let uu____6058 = parse_interactive_query query_str in
        js_repl_eval st uu____6058 in
      match uu____6049 with
      | (js_response, st_opt) ->
          let uu____6077 = FStar_Util.string_of_json js_response in
          (uu____6077, st_opt)
let (js_repl_init_opts : unit -> unit) =
  fun uu____6086 ->
    let uu____6087 = FStar_Options.parse_cmd_line () in
    match uu____6087 with
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
              | h::uu____6102::uu____6103 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____6106 -> ()))
let rec (go : FStar_Interactive_JsonHelper.repl_state -> Prims.int) =
  fun st ->
    let query1 =
      read_interactive_query st.FStar_Interactive_JsonHelper.repl_stdin in
    let uu____6115 = validate_and_run_query st query1 in
    match uu____6115 with
    | ((status, response), state_opt) ->
        (write_response query1.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref [] in
  let add_one e =
    let uu____6159 =
      let uu____6162 = FStar_ST.op_Bang issues in e :: uu____6162 in
    FStar_ST.op_Colon_Equals issues uu____6159 in
  let count_errors uu____6190 =
    let issues1 =
      let uu____6194 = FStar_ST.op_Bang issues in
      FStar_Util.remove_dups (fun i0 -> fun i1 -> i0 = i1) uu____6194 in
    let uu____6211 =
      FStar_List.filter
        (fun e -> e.FStar_Errors.issue_level = FStar_Errors.EError) issues1 in
    FStar_List.length uu____6211 in
  let report uu____6223 =
    let uu____6224 =
      let uu____6227 = FStar_ST.op_Bang issues in
      FStar_Util.remove_dups (fun i0 -> fun i1 -> i0 = i1) uu____6227 in
    FStar_List.sortWith FStar_Errors.compare_issues uu____6224 in
  let clear uu____6249 = FStar_ST.op_Colon_Equals issues [] in
  {
    FStar_Errors.eh_add_one = add_one;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report;
    FStar_Errors.eh_clear = clear
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
               let uu____6288 = get_json () in
               forward_message printer label uu____6288)
    }
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
let (initial_range : FStar_Range.range) =
  let uu____6300 = FStar_Range.mk_pos Prims.int_one Prims.int_zero in
  let uu____6301 = FStar_Range.mk_pos Prims.int_one Prims.int_zero in
  FStar_Range.mk_range "<input>" uu____6300 uu____6301
let (build_initial_repl_state :
  Prims.string -> FStar_Interactive_JsonHelper.repl_state) =
  fun filename ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range in
    let uu____6309 = FStar_Util.open_stdin () in
    {
      FStar_Interactive_JsonHelper.repl_line = Prims.int_one;
      FStar_Interactive_JsonHelper.repl_column = Prims.int_zero;
      FStar_Interactive_JsonHelper.repl_fname = filename;
      FStar_Interactive_JsonHelper.repl_deps_stack = [];
      FStar_Interactive_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_Interactive_JsonHelper.repl_env = env1;
      FStar_Interactive_JsonHelper.repl_stdin = uu____6309;
      FStar_Interactive_JsonHelper.repl_names =
        FStar_Interactive_CompletionTable.empty
    }
let interactive_mode' :
  'uuuuuu6322 . FStar_Interactive_JsonHelper.repl_state -> 'uuuuuu6322 =
  fun init_st ->
    write_hello ();
    (let exit_code =
       let uu____6330 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu____6330
       then
         let uu____6331 =
           let uu____6332 = FStar_Options.file_list () in
           FStar_List.hd uu____6332 in
         FStar_SMTEncoding_Solver.with_hints_db uu____6331
           (fun uu____6336 -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let (interactive_mode : Prims.string -> unit) =
  fun filename ->
    install_ide_mode_hooks FStar_Interactive_JsonHelper.write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____6346 =
       let uu____6347 = FStar_Options.codegen () in
       FStar_Option.isSome uu____6347 in
     if uu____6346
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init = build_initial_repl_state filename in
     let uu____6352 = FStar_Options.trace_error () in
     if uu____6352
     then interactive_mode' init
     else
       (try
          (fun uu___1077_6355 -> match () with | () -> interactive_mode' init)
            ()
        with
        | uu___1076_6358 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___1076_6358)))