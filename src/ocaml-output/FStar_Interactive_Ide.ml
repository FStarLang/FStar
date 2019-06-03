open Prims
let with_captured_errors' :
  'Auu____28 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____28 FStar_Pervasives_Native.option)
          -> 'Auu____28 FStar_Pervasives_Native.option
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
            ((let uu____82 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.log_issue uu____82
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e, msg, r) ->
            (FStar_Errors.add_errors [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e, msg) ->
            ((let uu____112 =
                let uu____122 =
                  let uu____130 = FStar_TypeChecker_Env.get_range env in
                  (e, msg, uu____130) in
                [uu____122] in
              FStar_Errors.add_errors uu____112);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop -> FStar_Pervasives_Native.None
let with_captured_errors :
  'Auu____155 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____155 FStar_Pervasives_Native.option)
          -> 'Auu____155 FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        let uu____182 = FStar_Options.trace_error () in
        if uu____182
        then f env
        else with_captured_errors' env sigint_handler f
let (t0 : FStar_Util.time) = FStar_Util.now ()
let (dummy_tf_of_fname : Prims.string -> FStar_JsonHelper.timed_fname) =
  fun fname ->
    { FStar_JsonHelper.tf_fname = fname; FStar_JsonHelper.tf_modtime = t0 }
let (string_of_timed_fname : FStar_JsonHelper.timed_fname -> Prims.string) =
  fun uu____204 ->
    match uu____204 with
    | { FStar_JsonHelper.tf_fname = fname;
        FStar_JsonHelper.tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____214 = FStar_Util.string_of_time modtime in
           FStar_Util.format2 "{ %s; %s }" fname uu____214)
type push_query =
  {
  push_kind: FStar_PushHelper.push_kind ;
  push_code: Prims.string ;
  push_line: Prims.int ;
  push_column: Prims.int ;
  push_peek_only: Prims.bool }
let (__proj__Mkpush_query__item__push_kind :
  push_query -> FStar_PushHelper.push_kind) =
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
let (nothing_left_to_pop : FStar_JsonHelper.repl_state -> Prims.bool) =
  fun st ->
    let uu____346 =
      let uu____347 = FStar_ST.op_Bang FStar_PushHelper.repl_stack in
      FStar_List.length uu____347 in
    uu____346 = (FStar_List.length st.FStar_JsonHelper.repl_deps_stack)
let (string_of_repl_task : FStar_JsonHelper.repl_task -> Prims.string) =
  fun uu___0_399 ->
    match uu___0_399 with
    | FStar_JsonHelper.LDInterleaved (intf, impl) ->
        let uu____403 = string_of_timed_fname intf in
        let uu____405 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____403 uu____405
    | FStar_JsonHelper.LDSingle intf_or_impl ->
        let uu____409 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu____409
    | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu____413 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____413
    | FStar_JsonHelper.PushFragment frag ->
        FStar_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
    | FStar_JsonHelper.Noop -> "Noop {}"
let (run_repl_transaction :
  FStar_JsonHelper.repl_state ->
    FStar_PushHelper.push_kind ->
      Prims.bool ->
        FStar_JsonHelper.repl_task ->
          (Prims.bool * FStar_JsonHelper.repl_state))
  =
  fun st ->
    fun push_kind ->
      fun must_rollback ->
        fun task ->
          let st1 =
            FStar_PushHelper.push_repl "run_repl_transaction" push_kind task
              st in
          let uu____449 =
            FStar_PushHelper.track_name_changes st1.FStar_JsonHelper.repl_env in
          match uu____449 with
          | (env, finish_name_tracking) ->
              let check_success uu____494 =
                (let uu____497 = FStar_Errors.get_err_count () in
                 uu____497 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback) in
              let uu____501 =
                let uu____509 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1 ->
                       let uu____523 =
                         FStar_PushHelper.run_repl_task
                           st1.FStar_JsonHelper.repl_curmod env1 task in
                       FStar_All.pipe_left
                         (fun _542 -> FStar_Pervasives_Native.Some _542)
                         uu____523) in
                match uu____509 with
                | FStar_Pervasives_Native.Some (curmod, env1) when
                    check_success () -> (curmod, env1, true)
                | uu____558 ->
                    ((st1.FStar_JsonHelper.repl_curmod), env, false) in
              (match uu____501 with
               | (curmod, env1, success) ->
                   let uu____577 = finish_name_tracking env1 in
                   (match uu____577 with
                    | (env2, name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___95_598 = st1 in
                              {
                                FStar_JsonHelper.repl_line =
                                  (uu___95_598.FStar_JsonHelper.repl_line);
                                FStar_JsonHelper.repl_column =
                                  (uu___95_598.FStar_JsonHelper.repl_column);
                                FStar_JsonHelper.repl_fname =
                                  (uu___95_598.FStar_JsonHelper.repl_fname);
                                FStar_JsonHelper.repl_deps_stack =
                                  (uu___95_598.FStar_JsonHelper.repl_deps_stack);
                                FStar_JsonHelper.repl_curmod = curmod;
                                FStar_JsonHelper.repl_env = env2;
                                FStar_JsonHelper.repl_stdin =
                                  (uu___95_598.FStar_JsonHelper.repl_stdin);
                                FStar_JsonHelper.repl_names =
                                  (uu___95_598.FStar_JsonHelper.repl_names)
                              } in
                            FStar_PushHelper.commit_name_tracking st2
                              name_events
                          else
                            FStar_PushHelper.pop_repl "run_repl_transaction"
                              st1 in
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
          let uu____645 = FStar_Options.debug_any () in
          if uu____645
          then
            let uu____648 = string_of_repl_task task in
            FStar_Util.print2 "%s %s" verb uu____648
          else () in
        let rec revert_many st1 uu___1_673 =
          match uu___1_673 with
          | [] -> st1
          | (_id, (task, _st'))::entries ->
              (debug1 "Reverting" task;
               (let st' =
                  FStar_PushHelper.pop_repl "run_repl_ls_transactions" st1 in
                let dep_graph1 =
                  FStar_TypeChecker_Env.dep_graph
                    st1.FStar_JsonHelper.repl_env in
                let st'1 =
                  let uu___121_726 = st' in
                  let uu____727 =
                    FStar_TypeChecker_Env.set_dep_graph
                      st'.FStar_JsonHelper.repl_env dep_graph1 in
                  {
                    FStar_JsonHelper.repl_line =
                      (uu___121_726.FStar_JsonHelper.repl_line);
                    FStar_JsonHelper.repl_column =
                      (uu___121_726.FStar_JsonHelper.repl_column);
                    FStar_JsonHelper.repl_fname =
                      (uu___121_726.FStar_JsonHelper.repl_fname);
                    FStar_JsonHelper.repl_deps_stack =
                      (uu___121_726.FStar_JsonHelper.repl_deps_stack);
                    FStar_JsonHelper.repl_curmod =
                      (uu___121_726.FStar_JsonHelper.repl_curmod);
                    FStar_JsonHelper.repl_env = uu____727;
                    FStar_JsonHelper.repl_stdin =
                      (uu___121_726.FStar_JsonHelper.repl_stdin);
                    FStar_JsonHelper.repl_names =
                      (uu___121_726.FStar_JsonHelper.repl_names)
                  } in
                revert_many st'1 entries)) in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([], []) -> FStar_Util.Inl st1
          | (task::tasks2, []) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____780 = FStar_Options.restore_cmd_line_options false in
                FStar_All.pipe_right uu____780 (fun a1 -> ()));
               (let timestamped_task =
                  FStar_PushHelper.update_task_timestamps task in
                let push_kind =
                  let uu____784 = FStar_Options.lax () in
                  if uu____784
                  then FStar_PushHelper.LaxCheck
                  else FStar_PushHelper.FullCheck in
                let uu____789 =
                  run_repl_transaction st1 push_kind false timestamped_task in
                match uu____789 with
                | (success, st2) ->
                    if success
                    then
                      let uu____809 =
                        let uu___146_810 = st2 in
                        let uu____811 =
                          FStar_ST.op_Bang FStar_PushHelper.repl_stack in
                        {
                          FStar_JsonHelper.repl_line =
                            (uu___146_810.FStar_JsonHelper.repl_line);
                          FStar_JsonHelper.repl_column =
                            (uu___146_810.FStar_JsonHelper.repl_column);
                          FStar_JsonHelper.repl_fname =
                            (uu___146_810.FStar_JsonHelper.repl_fname);
                          FStar_JsonHelper.repl_deps_stack = uu____811;
                          FStar_JsonHelper.repl_curmod =
                            (uu___146_810.FStar_JsonHelper.repl_curmod);
                          FStar_JsonHelper.repl_env =
                            (uu___146_810.FStar_JsonHelper.repl_env);
                          FStar_JsonHelper.repl_stdin =
                            (uu___146_810.FStar_JsonHelper.repl_stdin);
                          FStar_JsonHelper.repl_names =
                            (uu___146_810.FStar_JsonHelper.repl_names)
                        } in
                      aux uu____809 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2, prev::previous1) when
              let uu____855 = FStar_PushHelper.update_task_timestamps task in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____855
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2, previous1) ->
              let uu____872 = revert_many st1 previous1 in
              aux uu____872 tasks2 [] in
        aux st tasks (FStar_List.rev st.FStar_JsonHelper.repl_deps_stack)
let (js_pushkind : FStar_Util.json -> FStar_PushHelper.push_kind) =
  fun s ->
    let uu____887 = FStar_JsonHelper.js_str s in
    match uu____887 with
    | "syntax" -> FStar_PushHelper.SyntaxCheck
    | "lax" -> FStar_PushHelper.LaxCheck
    | "full" -> FStar_PushHelper.FullCheck
    | uu____892 -> FStar_JsonHelper.js_fail "push_kind" s
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s ->
    let uu____901 = FStar_JsonHelper.js_str s in
    match uu____901 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____909 -> FStar_JsonHelper.js_fail "reduction rule" s
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKCode -> true | uu____938 -> false
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKOption _0 -> true | uu____951 -> false
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKOption _0 -> _0
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____979 -> false
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee -> match projectee with | CKModuleOrNamespace _0 -> _0
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1017 = FStar_JsonHelper.js_str k1 in
        (match uu____1017 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____1045 ->
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
    match projectee with | LKSymbolOnly -> true | uu____1057 -> false
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKModule -> true | uu____1068 -> false
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKOption -> true | uu____1079 -> false
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKCode -> true | uu____1090 -> false
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1103 = FStar_JsonHelper.js_str k1 in
        (match uu____1103 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____1113 ->
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
  fun projectee -> match projectee with | Exit -> true | uu____1230 -> false
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeProtocol -> true | uu____1241 -> false
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeRepl -> true | uu____1252 -> false
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Segment _0 -> true | uu____1265 -> false
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Segment _0 -> _0
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee -> match projectee with | Pop -> true | uu____1286 -> false
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Push _0 -> true | uu____1298 -> false
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | VfsAdd _0 -> true | uu____1325 -> false
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee -> match projectee with | VfsAdd _0 -> _0
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | AutoComplete _0 -> true | uu____1373 -> false
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee -> match projectee with | AutoComplete _0 -> _0
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Lookup _0 -> true | uu____1421 -> false
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee -> match projectee with | Lookup _0 -> _0
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Compute _0 -> true | uu____1491 -> false
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Compute _0 -> _0
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Search _0 -> true | uu____1538 -> false
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Search _0 -> _0
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | GenericError _0 -> true | uu____1561 -> false
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | GenericError _0 -> _0
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | ProtocolViolation _0 -> true | uu____1584 -> false
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | ProtocolViolation _0 -> _0
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee -> match projectee with | { qq; qid;_} -> qq
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee -> match projectee with | { qq; qid;_} -> qid
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___2_1622 ->
    match uu___2_1622 with
    | Exit -> false
    | DescribeProtocol -> false
    | DescribeRepl -> false
    | Segment uu____1627 -> false
    | Pop -> false
    | Push
        { push_kind = uu____1631; push_code = uu____1632;
          push_line = uu____1633; push_column = uu____1634;
          push_peek_only = false;_}
        -> false
    | VfsAdd uu____1640 -> false
    | GenericError uu____1650 -> false
    | ProtocolViolation uu____1653 -> false
    | Push uu____1656 -> true
    | AutoComplete uu____1658 -> true
    | Lookup uu____1665 -> true
    | Compute uu____1681 -> true
    | Search uu____1692 -> true
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
    match projectee with | QueryOK -> true | uu____1754 -> false
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryNOK -> true | uu____1765 -> false
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with
    | QueryViolatesProtocol -> true
    | uu____1776 -> false
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____1798 =
          let uu____1799 =
            let uu____1801 = FStar_JsonHelper.json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1801 in
          ProtocolViolation uu____1799 in
        { qq = uu____1798; qid }
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json ->
    let assoc1 errloc key a =
      let uu____1844 = FStar_JsonHelper.try_assoc key a in
      match uu____1844 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____1848 =
            let uu____1849 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            FStar_JsonHelper.InvalidQuery uu____1849 in
          FStar_Exn.raise uu____1848 in
    let request = FStar_All.pipe_right json FStar_JsonHelper.js_assoc in
    let qid =
      let uu____1869 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____1869 FStar_JsonHelper.js_str in
    try
      (fun uu___259_1879 ->
         match () with
         | () ->
             let query =
               let uu____1882 = assoc1 "query" "query" request in
               FStar_All.pipe_right uu____1882 FStar_JsonHelper.js_str in
             let args =
               let uu____1894 = assoc1 "query" "args" request in
               FStar_All.pipe_right uu____1894 FStar_JsonHelper.js_assoc in
             let arg1 k = assoc1 "[args]" k args in
             let try_arg k =
               let uu____1923 = FStar_JsonHelper.try_assoc k args in
               match uu____1923 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull) ->
                   FStar_Pervasives_Native.None
               | other -> other in
             let uu____1931 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____1937 =
                     let uu____1939 = arg1 "code" in
                     FStar_All.pipe_right uu____1939 FStar_JsonHelper.js_str in
                   Segment uu____1937
               | "peek" ->
                   let uu____1943 =
                     let uu____1944 =
                       let uu____1945 = arg1 "kind" in
                       FStar_All.pipe_right uu____1945 js_pushkind in
                     let uu____1947 =
                       let uu____1949 = arg1 "code" in
                       FStar_All.pipe_right uu____1949
                         FStar_JsonHelper.js_str in
                     let uu____1952 =
                       let uu____1954 = arg1 "line" in
                       FStar_All.pipe_right uu____1954
                         FStar_JsonHelper.js_int in
                     let uu____1957 =
                       let uu____1959 = arg1 "column" in
                       FStar_All.pipe_right uu____1959
                         FStar_JsonHelper.js_int in
                     {
                       push_kind = uu____1944;
                       push_code = uu____1947;
                       push_line = uu____1952;
                       push_column = uu____1957;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____1943
               | "push" ->
                   let uu____1965 =
                     let uu____1966 =
                       let uu____1967 = arg1 "kind" in
                       FStar_All.pipe_right uu____1967 js_pushkind in
                     let uu____1969 =
                       let uu____1971 = arg1 "code" in
                       FStar_All.pipe_right uu____1971
                         FStar_JsonHelper.js_str in
                     let uu____1974 =
                       let uu____1976 = arg1 "line" in
                       FStar_All.pipe_right uu____1976
                         FStar_JsonHelper.js_int in
                     let uu____1979 =
                       let uu____1981 = arg1 "column" in
                       FStar_All.pipe_right uu____1981
                         FStar_JsonHelper.js_int in
                     {
                       push_kind = uu____1966;
                       push_code = uu____1969;
                       push_line = uu____1974;
                       push_column = uu____1979;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____1965
               | "autocomplete" ->
                   let uu____1987 =
                     let uu____1993 =
                       let uu____1995 = arg1 "partial-symbol" in
                       FStar_All.pipe_right uu____1995
                         FStar_JsonHelper.js_str in
                     let uu____1998 =
                       let uu____1999 = try_arg "context" in
                       FStar_All.pipe_right uu____1999
                         js_optional_completion_context in
                     (uu____1993, uu____1998) in
                   AutoComplete uu____1987
               | "lookup" ->
                   let uu____2007 =
                     let uu____2022 =
                       let uu____2024 = arg1 "symbol" in
                       FStar_All.pipe_right uu____2024
                         FStar_JsonHelper.js_str in
                     let uu____2027 =
                       let uu____2028 = try_arg "context" in
                       FStar_All.pipe_right uu____2028
                         js_optional_lookup_context in
                     let uu____2034 =
                       let uu____2037 =
                         let uu____2047 = try_arg "location" in
                         FStar_All.pipe_right uu____2047
                           (FStar_Util.map_option FStar_JsonHelper.js_assoc) in
                       FStar_All.pipe_right uu____2037
                         (FStar_Util.map_option
                            (fun loc ->
                               let uu____2108 =
                                 let uu____2110 =
                                   assoc1 "[location]" "filename" loc in
                                 FStar_All.pipe_right uu____2110
                                   FStar_JsonHelper.js_str in
                               let uu____2114 =
                                 let uu____2116 =
                                   assoc1 "[location]" "line" loc in
                                 FStar_All.pipe_right uu____2116
                                   FStar_JsonHelper.js_int in
                               let uu____2120 =
                                 let uu____2122 =
                                   assoc1 "[location]" "column" loc in
                                 FStar_All.pipe_right uu____2122
                                   FStar_JsonHelper.js_int in
                               (uu____2108, uu____2114, uu____2120))) in
                     let uu____2129 =
                       let uu____2133 = arg1 "requested-info" in
                       FStar_All.pipe_right uu____2133
                         (FStar_JsonHelper.js_list FStar_JsonHelper.js_str) in
                     (uu____2022, uu____2027, uu____2034, uu____2129) in
                   Lookup uu____2007
               | "compute" ->
                   let uu____2146 =
                     let uu____2156 =
                       let uu____2158 = arg1 "term" in
                       FStar_All.pipe_right uu____2158
                         FStar_JsonHelper.js_str in
                     let uu____2161 =
                       let uu____2166 = try_arg "rules" in
                       FStar_All.pipe_right uu____2166
                         (FStar_Util.map_option
                            (FStar_JsonHelper.js_list js_reductionrule)) in
                     (uu____2156, uu____2161) in
                   Compute uu____2146
               | "search" ->
                   let uu____2184 =
                     let uu____2186 = arg1 "terms" in
                     FStar_All.pipe_right uu____2186 FStar_JsonHelper.js_str in
                   Search uu____2184
               | "vfs-add" ->
                   let uu____2190 =
                     let uu____2199 =
                       let uu____2203 = try_arg "filename" in
                       FStar_All.pipe_right uu____2203
                         (FStar_Util.map_option FStar_JsonHelper.js_str) in
                     let uu____2213 =
                       let uu____2215 = arg1 "contents" in
                       FStar_All.pipe_right uu____2215
                         FStar_JsonHelper.js_str in
                     (uu____2199, uu____2213) in
                   VfsAdd uu____2190
               | uu____2222 ->
                   let uu____2224 =
                     FStar_Util.format1 "Unknown query '%s'" query in
                   ProtocolViolation uu____2224 in
             { qq = uu____1931; qid }) ()
    with
    | FStar_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure qid expected got
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query ->
    try
      (fun uu___294_2243 ->
         match () with | () -> unpack_interactive_query js_query) ()
    with
    | FStar_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid = "?" }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure "?" expected got
let (parse_interactive_query : Prims.string -> query) =
  fun query_str ->
    let uu____2263 = FStar_Util.json_of_string query_str in
    match uu____2263 with
    | FStar_Pervasives_Native.None ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream ->
    let uu____2275 = FStar_Util.read_line stream in
    match uu____2275 with
    | FStar_Pervasives_Native.None -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
let json_of_opt :
  'Auu____2291 .
    ('Auu____2291 -> FStar_Util.json) ->
      'Auu____2291 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a ->
    fun opt_a ->
      let uu____2311 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2311
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
    let uu____2331 =
      let uu____2339 =
        let uu____2347 =
          let uu____2355 =
            let uu____2361 =
              let uu____2362 =
                let uu____2365 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2371 = FStar_Range.json_of_use_range r in
                      [uu____2371] in
                let uu____2372 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____2378 = FStar_Range.def_range r in
                      let uu____2379 = FStar_Range.use_range r in
                      uu____2378 <> uu____2379 ->
                      let uu____2380 = FStar_Range.json_of_def_range r in
                      [uu____2380]
                  | uu____2381 -> [] in
                FStar_List.append uu____2365 uu____2372 in
              FStar_Util.JsonList uu____2362 in
            ("ranges", uu____2361) in
          [uu____2355] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2347 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2339 in
    FStar_Util.JsonAssoc uu____2331
let (alist_of_symbol_lookup_result :
  FStar_QueryHelper.sl_reponse -> (Prims.string * FStar_Util.json) Prims.list)
  =
  fun lr ->
    let uu____2423 =
      let uu____2431 =
        let uu____2437 =
          json_of_opt FStar_Range.json_of_def_range
            lr.FStar_QueryHelper.slr_def_range in
        ("defined-at", uu____2437) in
      let uu____2440 =
        let uu____2448 =
          let uu____2454 =
            json_of_opt (fun _2456 -> FStar_Util.JsonStr _2456)
              lr.FStar_QueryHelper.slr_typ in
          ("type", uu____2454) in
        let uu____2459 =
          let uu____2467 =
            let uu____2473 =
              json_of_opt (fun _2475 -> FStar_Util.JsonStr _2475)
                lr.FStar_QueryHelper.slr_doc in
            ("documentation", uu____2473) in
          let uu____2478 =
            let uu____2486 =
              let uu____2492 =
                json_of_opt (fun _2494 -> FStar_Util.JsonStr _2494)
                  lr.FStar_QueryHelper.slr_def in
              ("definition", uu____2492) in
            [uu____2486] in
          uu____2467 :: uu____2478 in
        uu____2448 :: uu____2459 in
      uu____2431 :: uu____2440 in
    ("name", (FStar_Util.JsonStr (lr.FStar_QueryHelper.slr_name))) ::
      uu____2423
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____2539 =
      FStar_List.map (fun _2543 -> FStar_Util.JsonStr _2543)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _2546 -> FStar_Util.JsonList _2546) uu____2539 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptSet -> true | uu____2575 -> false
let (uu___is_OptReset : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReset -> true | uu____2586 -> false
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReadOnly -> true | uu____2597 -> false
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___3_2605 ->
    match uu___3_2605 with
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
  fun uu___4_2856 ->
    match uu___4_2856 with
    | FStar_Options.Const uu____2858 -> "flag"
    | FStar_Options.IntStr uu____2860 -> "int"
    | FStar_Options.BoolStr -> "bool"
    | FStar_Options.PathStr uu____2864 -> "path"
    | FStar_Options.SimpleStr uu____2867 -> "string"
    | FStar_Options.EnumStr uu____2870 -> "enum"
    | FStar_Options.OpenEnumStr uu____2875 -> "open enum"
    | FStar_Options.PostProcessed (uu____2885, typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____2895, typ) ->
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
        | FStar_Options.Const uu____2967 -> [""]
        | FStar_Options.BoolStr -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs, desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____3005, elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____3015, elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____3023 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____3023
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___5_3034 ->
    match uu___5_3034 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____3046 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____3046
    | FStar_Options.Unset -> FStar_Util.JsonNull
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt ->
    let uu____3062 =
      let uu____3070 =
        let uu____3078 =
          let uu____3084 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____3084) in
        let uu____3087 =
          let uu____3095 =
            let uu____3101 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____3101) in
          let uu____3104 =
            let uu____3112 =
              let uu____3118 =
                json_of_opt (fun _3120 -> FStar_Util.JsonStr _3120)
                  opt.opt_documentation in
              ("documentation", uu____3118) in
            let uu____3123 =
              let uu____3131 =
                let uu____3137 =
                  let uu____3138 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____3138 in
                ("type", uu____3137) in
              [uu____3131;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____3112 :: uu____3123 in
          uu____3095 :: uu____3104 in
        uu____3078 :: uu____3087 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____3070 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3062
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt ->
    let uu____3194 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____3194
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
      let uu____3290 =
        let uu____3298 =
          let uu____3306 =
            let uu____3312 =
              let uu____3313 = FStar_ST.op_Bang repl_current_qid in
              json_of_opt (fun _3343 -> FStar_Util.JsonStr _3343) uu____3313 in
            ("query-id", uu____3312) in
          [uu____3306;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)] in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____3298 in
      FStar_Util.JsonAssoc uu____3290
let forward_message :
  'Auu____3387 .
    (FStar_Util.json -> 'Auu____3387) ->
      Prims.string -> FStar_Util.json -> 'Auu____3387
  =
  fun callback ->
    fun level ->
      fun contents ->
        let uu____3410 = json_of_message level contents in
        callback uu____3410
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3414 =
      FStar_List.map (fun _3418 -> FStar_Util.JsonStr _3418)
        interactive_protocol_features in
    FStar_Util.JsonList uu____3414 in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
let (write_hello : unit -> unit) =
  fun uu____3432 -> FStar_JsonHelper.write_json json_of_hello
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name ->
    fun typ ->
      let flag = Prims.op_Hat "--" name in
      let uu____3450 = FStar_Options.desc_of_opt_type typ in
      match uu____3450 with
      | FStar_Pervasives_Native.None -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____3466 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____3501 ->
            match uu____3501 with
            | (_shortname, name, typ, doc1) ->
                let uu____3525 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____3525
                  (FStar_Util.map_option
                     (fun default_value ->
                        let uu____3537 = sig_of_fstar_option name typ in
                        let uu____3539 = snippets_of_fstar_option name typ in
                        let uu____3543 =
                          let uu____3544 = FStar_Options.settable name in
                          if uu____3544
                          then OptSet
                          else
                            (let uu____3549 = FStar_Options.resettable name in
                             if uu____3549 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____3537;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____3539;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____3543
                        })))) in
  FStar_All.pipe_right uu____3466
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
    let uu___466_3588 = opt in
    let uu____3589 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___466_3588.opt_name);
      opt_sig = (uu___466_3588.opt_sig);
      opt_value = uu____3589;
      opt_default = (uu___466_3588.opt_default);
      opt_type = (uu___466_3588.opt_type);
      opt_snippets = (uu___466_3588.opt_snippets);
      opt_documentation = (uu___466_3588.opt_documentation);
      opt_permission_level = (uu___466_3588.opt_permission_level)
    }
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1 ->
    let uu____3605 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____3605
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____3632 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____3632)
    else ("", opt_name)
let (json_of_repl_state : FStar_JsonHelper.repl_state -> FStar_Util.json) =
  fun st ->
    let filenames uu____3663 =
      match uu____3663 with
      | (uu____3675, (task, uu____3677)) ->
          (match task with
           | FStar_JsonHelper.LDInterleaved (intf, impl) ->
               [intf.FStar_JsonHelper.tf_fname;
               impl.FStar_JsonHelper.tf_fname]
           | FStar_JsonHelper.LDSingle intf_or_impl ->
               [intf_or_impl.FStar_JsonHelper.tf_fname]
           | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
               [intf.FStar_JsonHelper.tf_fname]
           | uu____3696 -> []) in
    let uu____3698 =
      let uu____3706 =
        let uu____3712 =
          let uu____3713 =
            let uu____3716 =
              FStar_List.concatMap filenames
                st.FStar_JsonHelper.repl_deps_stack in
            FStar_List.map (fun _3730 -> FStar_Util.JsonStr _3730) uu____3716 in
          FStar_Util.JsonList uu____3713 in
        ("loaded-dependencies", uu____3712) in
      let uu____3733 =
        let uu____3741 =
          let uu____3747 =
            let uu____3748 =
              let uu____3751 = current_fstar_options (fun uu____3756 -> true) in
              FStar_List.map json_of_fstar_option uu____3751 in
            FStar_Util.JsonList uu____3748 in
          ("options", uu____3747) in
        [uu____3741] in
      uu____3706 :: uu____3733 in
    FStar_Util.JsonAssoc uu____3698
let run_exit :
  'Auu____3782 'Auu____3783 .
    'Auu____3782 ->
      ((query_status * FStar_Util.json) * ('Auu____3783, Prims.int)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol :
  'Auu____3820 'Auu____3821 .
    'Auu____3820 ->
      ((query_status * FStar_Util.json) * ('Auu____3820, 'Auu____3821)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl :
  'Auu____3852 .
    FStar_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
        'Auu____3852) FStar_Util.either)
  =
  fun st ->
    let uu____3870 =
      let uu____3875 = json_of_repl_state st in (QueryOK, uu____3875) in
    (uu____3870, (FStar_Util.Inl st))
let run_protocol_violation :
  'Auu____3893 'Auu____3894 .
    'Auu____3893 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____3893, 'Auu____3894)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error :
  'Auu____3936 'Auu____3937 .
    'Auu____3936 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____3936, 'Auu____3937)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____3977 ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_segment :
  'Auu____3989 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____3989) FStar_Util.either)
  =
  fun st ->
    fun code ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_fname = "<input>";
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
          FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
        } in
      let collect_decls uu____4025 =
        let uu____4026 = FStar_Parser_Driver.parse_fragment frag in
        match uu____4026 with
        | FStar_Parser_Driver.Empty -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____4032, decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____4038, decls, uu____4040)) -> decls in
      let uu____4047 =
        with_captured_errors st.FStar_JsonHelper.repl_env
          FStar_Util.sigint_ignore
          (fun uu____4056 ->
             let uu____4057 = collect_decls () in
             FStar_All.pipe_left
               (fun _4068 -> FStar_Pervasives_Native.Some _4068) uu____4057) in
      match uu____4047 with
      | FStar_Pervasives_Native.None ->
          let errors =
            let uu____4086 = collect_errors () in
            FStar_All.pipe_right uu____4086 (FStar_List.map json_of_issue) in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____4112 =
              let uu____4120 =
                let uu____4126 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl) in
                ("def_range", uu____4126) in
              [uu____4120] in
            FStar_Util.JsonAssoc uu____4112 in
          let js_decls =
            let uu____4140 = FStar_List.map json_of_decl decls in
            FStar_All.pipe_left (fun _4145 -> FStar_Util.JsonList _4145)
              uu____4140 in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
let run_vfs_add :
  'Auu____4175 .
    FStar_JsonHelper.repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
            'Auu____4175) FStar_Util.either)
  =
  fun st ->
    fun opt_fname ->
      fun contents ->
        let fname = FStar_Util.dflt st.FStar_JsonHelper.repl_fname opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop :
  'Auu____4228 .
    FStar_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
        'Auu____4228) FStar_Util.either)
  =
  fun st ->
    let uu____4246 = nothing_left_to_pop st in
    if uu____4246
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let st' = FStar_PushHelper.pop_repl "pop_query" st in
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
      let uu____4333 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents) in
      FStar_JsonHelper.write_json uu____4333
let (write_repl_ld_task_progress : FStar_JsonHelper.repl_task -> unit) =
  fun task ->
    match task with
    | FStar_JsonHelper.LDInterleaved (uu____4341, tf) ->
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
    | uu____4393 -> ()
let (load_deps :
  FStar_JsonHelper.repl_state ->
    ((FStar_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st ->
    let uu____4411 =
      with_captured_errors st.FStar_JsonHelper.repl_env
        FStar_Util.sigint_ignore
        (fun _env ->
           let uu____4439 =
             FStar_PushHelper.deps_and_repl_ld_tasks_of_our_file
               st.FStar_JsonHelper.repl_fname in
           FStar_All.pipe_left
             (fun _4486 -> FStar_Pervasives_Native.Some _4486) uu____4439) in
    match uu____4411 with
    | FStar_Pervasives_Native.None -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) ->
        let st1 =
          let uu___556_4541 = st in
          let uu____4542 =
            FStar_TypeChecker_Env.set_dep_graph st.FStar_JsonHelper.repl_env
              dep_graph1 in
          {
            FStar_JsonHelper.repl_line =
              (uu___556_4541.FStar_JsonHelper.repl_line);
            FStar_JsonHelper.repl_column =
              (uu___556_4541.FStar_JsonHelper.repl_column);
            FStar_JsonHelper.repl_fname =
              (uu___556_4541.FStar_JsonHelper.repl_fname);
            FStar_JsonHelper.repl_deps_stack =
              (uu___556_4541.FStar_JsonHelper.repl_deps_stack);
            FStar_JsonHelper.repl_curmod =
              (uu___556_4541.FStar_JsonHelper.repl_curmod);
            FStar_JsonHelper.repl_env = uu____4542;
            FStar_JsonHelper.repl_stdin =
              (uu___556_4541.FStar_JsonHelper.repl_stdin);
            FStar_JsonHelper.repl_names =
              (uu___556_4541.FStar_JsonHelper.repl_names)
          } in
        let uu____4543 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress in
        (match uu____4543 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue ->
    let uu___566_4598 = issue in
    let uu____4599 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____4599;
      FStar_Errors.issue_level = (uu___566_4598.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___566_4598.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___566_4598.FStar_Errors.issue_number)
    }
let run_push_without_deps :
  'Auu____4609 .
    FStar_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____4609) FStar_Util.either)
  =
  fun st ->
    fun query ->
      let set_nosynth_flag st1 flag =
        let uu___573_4645 = st1 in
        {
          FStar_JsonHelper.repl_line =
            (uu___573_4645.FStar_JsonHelper.repl_line);
          FStar_JsonHelper.repl_column =
            (uu___573_4645.FStar_JsonHelper.repl_column);
          FStar_JsonHelper.repl_fname =
            (uu___573_4645.FStar_JsonHelper.repl_fname);
          FStar_JsonHelper.repl_deps_stack =
            (uu___573_4645.FStar_JsonHelper.repl_deps_stack);
          FStar_JsonHelper.repl_curmod =
            (uu___573_4645.FStar_JsonHelper.repl_curmod);
          FStar_JsonHelper.repl_env =
            (let uu___575_4647 = st1.FStar_JsonHelper.repl_env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___575_4647.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___575_4647.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___575_4647.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___575_4647.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___575_4647.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___575_4647.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___575_4647.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___575_4647.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___575_4647.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___575_4647.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___575_4647.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___575_4647.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___575_4647.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___575_4647.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___575_4647.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___575_4647.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___575_4647.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___575_4647.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___575_4647.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___575_4647.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___575_4647.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___575_4647.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___575_4647.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___575_4647.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___575_4647.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___575_4647.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___575_4647.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___575_4647.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___575_4647.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___575_4647.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___575_4647.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___575_4647.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___575_4647.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___575_4647.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___575_4647.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___575_4647.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___575_4647.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___575_4647.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___575_4647.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___575_4647.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___575_4647.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___575_4647.FStar_TypeChecker_Env.nbe)
             });
          FStar_JsonHelper.repl_stdin =
            (uu___573_4645.FStar_JsonHelper.repl_stdin);
          FStar_JsonHelper.repl_names =
            (uu___573_4645.FStar_JsonHelper.repl_names)
        } in
      let uu____4648 = query in
      match uu____4648 with
      | { push_kind; push_code = text; push_line = line;
          push_column = column; push_peek_only = peek_only;_} ->
          let frag =
            {
              FStar_Parser_ParseIt.frag_fname = "<input>";
              FStar_Parser_ParseIt.frag_text = text;
              FStar_Parser_ParseIt.frag_line = line;
              FStar_Parser_ParseIt.frag_col = column
            } in
          (FStar_TypeChecker_Env.toggle_id_info st.FStar_JsonHelper.repl_env
             true;
           (let st1 = set_nosynth_flag st peek_only in
            let uu____4675 =
              run_repl_transaction st1 push_kind peek_only
                (FStar_JsonHelper.PushFragment frag) in
            match uu____4675 with
            | (success, st2) ->
                let st3 = set_nosynth_flag st2 false in
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu____4704 =
                    let uu____4707 = collect_errors () in
                    FStar_All.pipe_right uu____4707
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu____4704 in
                let st4 =
                  if success
                  then
                    let uu___594_4716 = st3 in
                    {
                      FStar_JsonHelper.repl_line = line;
                      FStar_JsonHelper.repl_column = column;
                      FStar_JsonHelper.repl_fname =
                        (uu___594_4716.FStar_JsonHelper.repl_fname);
                      FStar_JsonHelper.repl_deps_stack =
                        (uu___594_4716.FStar_JsonHelper.repl_deps_stack);
                      FStar_JsonHelper.repl_curmod =
                        (uu___594_4716.FStar_JsonHelper.repl_curmod);
                      FStar_JsonHelper.repl_env =
                        (uu___594_4716.FStar_JsonHelper.repl_env);
                      FStar_JsonHelper.repl_stdin =
                        (uu___594_4716.FStar_JsonHelper.repl_stdin);
                      FStar_JsonHelper.repl_names =
                        (uu___594_4716.FStar_JsonHelper.repl_names)
                    }
                  else st3 in
                ((status, json_errors), (FStar_Util.Inl st4))))
let run_push_with_deps :
  'Auu____4734 .
    FStar_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____4734) FStar_Util.either)
  =
  fun st ->
    fun query ->
      (let uu____4758 = FStar_Options.debug_any () in
       if uu____4758
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.FStar_JsonHelper.repl_env false;
      (let uu____4766 = load_deps st in
       match uu____4766 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____4801 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu____4801 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1, deps) ->
           ((let uu____4835 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____4835 (fun a2 -> ()));
            (let names1 =
               FStar_PushHelper.add_module_completions
                 st1.FStar_JsonHelper.repl_fname deps
                 st1.FStar_JsonHelper.repl_names in
             run_push_without_deps
               (let uu___612_4839 = st1 in
                {
                  FStar_JsonHelper.repl_line =
                    (uu___612_4839.FStar_JsonHelper.repl_line);
                  FStar_JsonHelper.repl_column =
                    (uu___612_4839.FStar_JsonHelper.repl_column);
                  FStar_JsonHelper.repl_fname =
                    (uu___612_4839.FStar_JsonHelper.repl_fname);
                  FStar_JsonHelper.repl_deps_stack =
                    (uu___612_4839.FStar_JsonHelper.repl_deps_stack);
                  FStar_JsonHelper.repl_curmod =
                    (uu___612_4839.FStar_JsonHelper.repl_curmod);
                  FStar_JsonHelper.repl_env =
                    (uu___612_4839.FStar_JsonHelper.repl_env);
                  FStar_JsonHelper.repl_stdin =
                    (uu___612_4839.FStar_JsonHelper.repl_stdin);
                  FStar_JsonHelper.repl_names = names1
                }) query)))
let run_push :
  'Auu____4847 .
    FStar_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____4847) FStar_Util.either)
  =
  fun st ->
    fun query ->
      let uu____4870 = nothing_left_to_pop st in
      if uu____4870
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
          let uu____4937 =
            FStar_QueryHelper.symlookup st.FStar_JsonHelper.repl_env symbol
              pos_opt requested_info in
          match uu____4937 with
          | FStar_Pervasives_Native.None -> FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some result ->
              let uu____4972 =
                let uu____4985 = alist_of_symbol_lookup_result result in
                ("symbol", uu____4985) in
              FStar_Util.Inr uu____4972
let (run_option_lookup :
  Prims.string ->
    (Prims.string,
      (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
      FStar_Util.either)
  =
  fun opt_name ->
    let uu____5040 = trim_option_name opt_name in
    match uu____5040 with
    | (uu____5064, trimmed_name) ->
        let uu____5070 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____5070 with
         | FStar_Pervasives_Native.None ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____5105 =
               let uu____5118 =
                 let uu____5126 = update_option opt in
                 alist_of_fstar_option uu____5126 in
               ("option", uu____5118) in
             FStar_Util.Inr uu____5105)
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
      let uu____5184 =
        FStar_Interactive_CompletionTable.find_module_or_ns
          st.FStar_JsonHelper.repl_names query in
      match uu____5184 with
      | FStar_Pervasives_Native.None ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____5219 =
            let uu____5232 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____5232) in
          FStar_Util.Inr uu____5219
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____5263 =
            let uu____5276 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____5276) in
          FStar_Util.Inr uu____5263
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
          let uu____5356 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____5356 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____5430 ->
              let uu____5445 = run_module_lookup st symbol in
              (match uu____5445 with
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
  'Auu____5633 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        lookup_context ->
          FStar_QueryHelper.position FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) *
                (FStar_JsonHelper.repl_state, 'Auu____5633)
                FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun context ->
        fun pos_opt ->
          fun requested_info ->
            let uu____5683 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____5683 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind, info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let run_code_autocomplete :
  'Auu____5789 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____5789) FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      let result = FStar_QueryHelper.ck_completion st search_term in
      let js =
        FStar_List.map
          FStar_Interactive_CompletionTable.json_of_completion_result result in
      ((QueryOK, (FStar_Util.JsonList js)), (FStar_Util.Inl st))
let run_module_autocomplete :
  'Auu____5843 'Auu____5844 'Auu____5845 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        'Auu____5843 ->
          'Auu____5844 ->
            ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
              'Auu____5845) FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun modules1 ->
        fun namespaces ->
          let needle = FStar_Util.split search_term "." in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.FStar_JsonHelper.repl_names needle
              (fun _5892 -> FStar_Pervasives_Native.Some _5892) in
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
        let uu____5926 =
          match opt.opt_permission_level with
          | OptSet -> (true, "")
          | OptReset -> (is_reset, "#reset-only")
          | OptReadOnly -> (false, "read-only") in
        match uu____5926 with
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
  'Auu____5989 'Auu____5990 .
    'Auu____5989 ->
      Prims.string ->
        Prims.bool ->
          ((query_status * FStar_Util.json) * ('Auu____5989, 'Auu____5990)
            FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun is_reset ->
        let uu____6022 = trim_option_name search_term in
        match uu____6022 with
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
        | (uu____6078, uu____6079) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete :
  'Auu____6102 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
            'Auu____6102) FStar_Util.either)
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
  'Auu____6153 'Auu____6154 .
    FStar_JsonHelper.repl_state ->
      'Auu____6153 ->
        (FStar_JsonHelper.repl_state -> 'Auu____6153) ->
          ('Auu____6153 * (FStar_JsonHelper.repl_state, 'Auu____6154)
            FStar_Util.either)
  =
  fun st ->
    fun sigint_default ->
      fun task ->
        let st1 =
          FStar_PushHelper.push_repl "run_and_rewind"
            FStar_PushHelper.FullCheck FStar_JsonHelper.Noop st in
        let results =
          try
            (fun uu___728_6195 ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____6206 ->
                        let uu____6207 = task st1 in
                        FStar_All.pipe_left
                          (fun _6212 -> FStar_Util.Inl _6212) uu____6207)) ()
          with | FStar_Util.SigInt -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e in
        let st2 = FStar_PushHelper.pop_repl "run_and_rewind" st1 in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
let run_with_parsed_and_tc_term :
  'Auu____6261 'Auu____6262 'Auu____6263 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        'Auu____6261 ->
          'Auu____6262 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) *
                (FStar_JsonHelper.repl_state, 'Auu____6263)
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
                FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0");
                FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
              } in
            let find_let_body ses =
              match ses with
              | {
                  FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                    ((uu____6365,
                      { FStar_Syntax_Syntax.lbname = uu____6366;
                        FStar_Syntax_Syntax.lbunivs = univs1;
                        FStar_Syntax_Syntax.lbtyp = uu____6368;
                        FStar_Syntax_Syntax.lbeff = uu____6369;
                        FStar_Syntax_Syntax.lbdef = def;
                        FStar_Syntax_Syntax.lbattrs = uu____6371;
                        FStar_Syntax_Syntax.lbpos = uu____6372;_}::[]),
                     uu____6373);
                  FStar_Syntax_Syntax.sigrng = uu____6374;
                  FStar_Syntax_Syntax.sigquals = uu____6375;
                  FStar_Syntax_Syntax.sigmeta = uu____6376;
                  FStar_Syntax_Syntax.sigattrs = uu____6377;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____6416 -> FStar_Pervasives_Native.None in
            let parse1 frag =
              let uu____6437 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag) in
              match uu____6437 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls, uu____6443) ->
                  FStar_Pervasives_Native.Some decls
              | uu____6464 -> FStar_Pervasives_Native.None in
            let desugar env decls =
              let uu____6482 =
                let uu____6487 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
                uu____6487 env.FStar_TypeChecker_Env.dsenv in
              FStar_Pervasives_Native.fst uu____6482 in
            let typecheck tcenv decls =
              let uu____6509 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
              match uu____6509 with | (ses, uu____6523, uu____6524) -> ses in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1 ->
                 let tcenv = st1.FStar_JsonHelper.repl_env in
                 let frag = dummy_let_fragment term in
                 let uu____6545 = parse1 frag in
                 match uu____6545 with
                 | FStar_Pervasives_Native.None ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____6571 =
                       let decls1 = desugar tcenv decls in
                       let ses = typecheck tcenv decls1 in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1, def) ->
                           let uu____6607 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def in
                           (match uu____6607 with
                            | (univs2, def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2 in
                                continuation tcenv1 def1) in
                     let uu____6619 = FStar_Options.trace_error () in
                     if uu____6619
                     then aux ()
                     else
                       (try
                          (fun uu___811_6633 -> match () with | () -> aux ())
                            ()
                        with
                        | uu___810_6642 ->
                            let uu____6647 =
                              FStar_Errors.issue_of_exn uu___810_6642 in
                            (match uu____6647 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____6655 =
                                   let uu____6656 =
                                     FStar_Errors.format_issue issue in
                                   FStar_Util.JsonStr uu____6656 in
                                 (QueryNOK, uu____6655)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Exn.raise uu___810_6642)))
let run_compute :
  'Auu____6671 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
            'Auu____6671) FStar_Util.either)
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
               let uu____6749 =
                 let uu____6750 =
                   FStar_QueryHelper.term_to_string tcenv normalized in
                 FStar_Util.JsonStr uu____6750 in
               (QueryOK, uu____6749))
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NameContainsStr _0 -> true | uu____6785 -> false
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee -> match projectee with | NameContainsStr _0 -> _0
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeContainsLid _0 -> true | uu____6807 -> false
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TypeContainsLid _0 -> _0
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | { st_negate; st_term;_} -> st_negate
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee -> match projectee with | { st_negate; st_term;_} -> st_term
let (st_cost : search_term' -> Prims.int) =
  fun uu___6_6842 ->
    match uu___6_6842 with
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
    let uu____6976 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____6983 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____6976; sc_fvars = uu____6983 }
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv ->
    fun sc ->
      let uu____7007 = FStar_ST.op_Bang sc.sc_typ in
      match uu____7007 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let typ =
            let uu____7035 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____7035 with
            | FStar_Pervasives_Native.None ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7054, typ), uu____7056) ->
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
      let uu____7106 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____7106 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None ->
          let fv =
            let uu____7150 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____7150 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv ->
    fun sc ->
      let typ_str =
        let uu____7194 = sc_typ tcenv sc in
        FStar_QueryHelper.term_to_string tcenv uu____7194 in
      let uu____7195 =
        let uu____7203 =
          let uu____7209 =
            let uu____7210 =
              let uu____7212 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              uu____7212.FStar_Ident.str in
            FStar_Util.JsonStr uu____7210 in
          ("lid", uu____7209) in
        [uu____7203; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu____7195
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidSearch uu____7245 -> true
    | uu____7248 -> false
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidSearch uu____7258 -> uu____7258
let run_search :
  'Auu____7267 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____7267) FStar_Util.either)
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
              let uu____7314 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____7314 in
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
              let uu____7373 =
                let uu____7374 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____7374 in
              FStar_Exn.raise uu____7373
            else
              if beg_quote
              then
                (let uu____7380 = strip_quotes term1 in
                 NameContainsStr uu____7380)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____7385 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu____7385 with
                 | FStar_Pervasives_Native.None ->
                     let uu____7388 =
                       let uu____7389 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____7389 in
                     FStar_Exn.raise uu____7388
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____7417 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____7417 in
      let results =
        try
          (fun uu___924_7451 ->
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
                        let uu____7499 = FStar_List.map pprint_one terms in
                        FStar_Util.concat_l " " uu____7499 in
                      let uu____7505 =
                        let uu____7506 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds in
                        InvalidSearch uu____7506 in
                      FStar_Exn.raise uu____7505
                  | uu____7513 -> (QueryOK, (FStar_Util.JsonList js)))) ()
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
          { push_kind = FStar_PushHelper.SyntaxCheck; push_code = uu____7644;
            push_line = uu____7645; push_column = uu____7646;
            push_peek_only = false;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____7652 ->
          (match st.FStar_JsonHelper.repl_curmod with
           | FStar_Pervasives_Native.None when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____7654 -> q)
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
      let uu____7727 = validate_and_run_query st query in
      match uu____7727 with
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
      let uu____7793 = deserialize_interactive_query query_js in
      js_repl_eval st uu____7793
let (js_repl_eval_str :
  FStar_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string * (FStar_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query_str ->
      let uu____7817 =
        let uu____7827 = parse_interactive_query query_str in
        js_repl_eval st uu____7827 in
      match uu____7817 with
      | (js_response, st_opt) ->
          let uu____7850 = FStar_Util.string_of_json js_response in
          (uu____7850, st_opt)
let (js_repl_init_opts : unit -> unit) =
  fun uu____7863 ->
    let uu____7864 = FStar_Options.parse_cmd_line () in
    match uu____7864 with
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
              | h::uu____7887::uu____7888 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____7897 -> ()))
let rec (go : FStar_JsonHelper.repl_state -> Prims.int) =
  fun st ->
    let query = read_interactive_query st.FStar_JsonHelper.repl_stdin in
    let uu____7910 = validate_and_run_query st query in
    match uu____7910 with
    | ((status, response), state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____7963 =
      let uu____7966 = FStar_ST.op_Bang issues in e :: uu____7966 in
    FStar_ST.op_Colon_Equals issues uu____7963 in
  let count_errors uu____8020 =
    let uu____8021 =
      let uu____8024 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____8024 in
    FStar_List.length uu____8021 in
  let report uu____8059 =
    let uu____8060 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____8060 in
  let clear1 uu____8091 = FStar_ST.op_Colon_Equals issues [] in
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
               let uu____8152 = get_json () in
               forward_message printer label uu____8152)
    }
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
let (initial_range : Prims.string -> FStar_Range.range) =
  fun fname ->
    let uu____8173 =
      FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
    let uu____8176 =
      FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
    FStar_Range.mk_range fname uu____8173 uu____8176
let (build_initial_repl_state : Prims.string -> FStar_JsonHelper.repl_state)
  =
  fun filename ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
    let env1 =
      let uu____8189 = initial_range filename in
      FStar_TypeChecker_Env.set_range env uu____8189 in
    let uu____8190 = FStar_Util.open_stdin () in
    {
      FStar_JsonHelper.repl_line = (Prims.parse_int "1");
      FStar_JsonHelper.repl_column = (Prims.parse_int "0");
      FStar_JsonHelper.repl_fname = filename;
      FStar_JsonHelper.repl_deps_stack = [];
      FStar_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_JsonHelper.repl_env = env1;
      FStar_JsonHelper.repl_stdin = uu____8190;
      FStar_JsonHelper.repl_names = FStar_Interactive_CompletionTable.empty
    }
let interactive_mode' :
  'Auu____8206 . FStar_JsonHelper.repl_state -> 'Auu____8206 =
  fun init_st ->
    write_hello ();
    (let exit_code =
       let uu____8215 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu____8215
       then
         let uu____8219 =
           let uu____8221 = FStar_Options.file_list () in
           FStar_List.hd uu____8221 in
         FStar_SMTEncoding_Solver.with_hints_db uu____8219
           (fun uu____8228 -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let (interactive_mode : Prims.string -> unit) =
  fun filename ->
    install_ide_mode_hooks FStar_JsonHelper.write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____8242 =
       let uu____8244 = FStar_Options.codegen () in
       FStar_Option.isSome uu____8244 in
     if uu____8242
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename in
     let uu____8253 = FStar_Options.trace_error () in
     if uu____8253
     then interactive_mode' init1
     else
       (try
          (fun uu___1073_8259 ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___1072_8262 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___1072_8262)))