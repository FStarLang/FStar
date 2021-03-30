open Prims
let with_captured_errors' :
  'uuuuu .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env -> 'uuuuu FStar_Pervasives_Native.option)
          -> 'uuuuu FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        try
          (fun uu___ ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu___1 -> f env)) ()
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
            ((let uu___2 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.log_issue uu___2
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e, msg, r, ctx) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r, ctx)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e, msg, ctx) ->
            ((let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_TypeChecker_Env.get_range env in
                  (e, msg, uu___4, ctx) in
                [uu___3] in
              FStar_TypeChecker_Err.add_errors env uu___2);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop -> FStar_Pervasives_Native.None
let with_captured_errors :
  'uuuuu .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env -> 'uuuuu FStar_Pervasives_Native.option)
          -> 'uuuuu FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        let uu___ = FStar_Options.trace_error () in
        if uu___ then f env else with_captured_errors' env sigint_handler f
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
  fun uu___ ->
    match uu___ with
    | { FStar_Interactive_JsonHelper.tf_fname = fname;
        FStar_Interactive_JsonHelper.tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu___2 = FStar_Util.string_of_time modtime in
           FStar_Util.format2 "{ %s; %s }" fname uu___2)
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
    let uu___ =
      let uu___1 = FStar_ST.op_Bang FStar_Interactive_PushHelper.repl_stack in
      FStar_List.length uu___1 in
    uu___ =
      (FStar_List.length st.FStar_Interactive_JsonHelper.repl_deps_stack)
let (string_of_repl_task :
  FStar_Interactive_JsonHelper.repl_task -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) ->
        let uu___1 = string_of_timed_fname intf in
        let uu___2 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu___1 uu___2
    | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
        let uu___1 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu___1
    | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu___1 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu___1
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
          let uu___ =
            FStar_Interactive_PushHelper.track_name_changes
              st1.FStar_Interactive_JsonHelper.repl_env in
          match uu___ with
          | (env, finish_name_tracking) ->
              let check_success uu___1 =
                (let uu___2 = FStar_Errors.get_err_count () in
                 uu___2 = Prims.int_zero) &&
                  (Prims.op_Negation must_rollback) in
              let uu___1 =
                let uu___2 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1 ->
                       let uu___3 =
                         FStar_Interactive_PushHelper.run_repl_task
                           st1.FStar_Interactive_JsonHelper.repl_curmod env1
                           task in
                       FStar_All.pipe_left
                         (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                         uu___3) in
                match uu___2 with
                | FStar_Pervasives_Native.Some (curmod, env1) when
                    check_success () -> (curmod, env1, true)
                | uu___3 ->
                    ((st1.FStar_Interactive_JsonHelper.repl_curmod), env,
                      false) in
              (match uu___1 with
               | (curmod, env1, success) ->
                   let uu___2 = finish_name_tracking env1 in
                   (match uu___2 with
                    | (env2, name_events) ->
                        let st2 =
                          if success
                          then
                            let st3 =
                              let uu___3 = st1 in
                              {
                                FStar_Interactive_JsonHelper.repl_line =
                                  (uu___3.FStar_Interactive_JsonHelper.repl_line);
                                FStar_Interactive_JsonHelper.repl_column =
                                  (uu___3.FStar_Interactive_JsonHelper.repl_column);
                                FStar_Interactive_JsonHelper.repl_fname =
                                  (uu___3.FStar_Interactive_JsonHelper.repl_fname);
                                FStar_Interactive_JsonHelper.repl_deps_stack
                                  =
                                  (uu___3.FStar_Interactive_JsonHelper.repl_deps_stack);
                                FStar_Interactive_JsonHelper.repl_curmod =
                                  curmod;
                                FStar_Interactive_JsonHelper.repl_env = env2;
                                FStar_Interactive_JsonHelper.repl_stdin =
                                  (uu___3.FStar_Interactive_JsonHelper.repl_stdin);
                                FStar_Interactive_JsonHelper.repl_names =
                                  (uu___3.FStar_Interactive_JsonHelper.repl_names)
                              } in
                            FStar_Interactive_PushHelper.commit_name_tracking
                              st3 name_events
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
          let uu___ = FStar_Options.debug_any () in
          if uu___
          then
            let uu___1 = string_of_repl_task task in
            FStar_Util.print2 "%s %s" verb uu___1
          else () in
        let rec revert_many st1 uu___ =
          match uu___ with
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
                  let uu___3 = st' in
                  let uu___4 =
                    FStar_TypeChecker_Env.set_dep_graph
                      st'.FStar_Interactive_JsonHelper.repl_env dep_graph in
                  {
                    FStar_Interactive_JsonHelper.repl_line =
                      (uu___3.FStar_Interactive_JsonHelper.repl_line);
                    FStar_Interactive_JsonHelper.repl_column =
                      (uu___3.FStar_Interactive_JsonHelper.repl_column);
                    FStar_Interactive_JsonHelper.repl_fname =
                      (uu___3.FStar_Interactive_JsonHelper.repl_fname);
                    FStar_Interactive_JsonHelper.repl_deps_stack =
                      (uu___3.FStar_Interactive_JsonHelper.repl_deps_stack);
                    FStar_Interactive_JsonHelper.repl_curmod =
                      (uu___3.FStar_Interactive_JsonHelper.repl_curmod);
                    FStar_Interactive_JsonHelper.repl_env = uu___4;
                    FStar_Interactive_JsonHelper.repl_stdin =
                      (uu___3.FStar_Interactive_JsonHelper.repl_stdin);
                    FStar_Interactive_JsonHelper.repl_names =
                      (uu___3.FStar_Interactive_JsonHelper.repl_names)
                  } in
                revert_many st'1 entries)) in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([], []) -> FStar_Util.Inl st1
          | (task::tasks2, []) ->
              (debug "Loading" task;
               progress_callback task;
               (let uu___3 = FStar_Options.restore_cmd_line_options false in
                FStar_All.pipe_right uu___3 (fun uu___4 -> ()));
               (let timestamped_task =
                  FStar_Interactive_PushHelper.update_task_timestamps task in
                let push_kind =
                  let uu___3 = FStar_Options.lax () in
                  if uu___3
                  then FStar_Interactive_PushHelper.LaxCheck
                  else FStar_Interactive_PushHelper.FullCheck in
                let uu___3 =
                  run_repl_transaction st1 push_kind false timestamped_task in
                match uu___3 with
                | (success, st2) ->
                    if success
                    then
                      let uu___4 =
                        let uu___5 = st2 in
                        let uu___6 =
                          FStar_ST.op_Bang
                            FStar_Interactive_PushHelper.repl_stack in
                        {
                          FStar_Interactive_JsonHelper.repl_line =
                            (uu___5.FStar_Interactive_JsonHelper.repl_line);
                          FStar_Interactive_JsonHelper.repl_column =
                            (uu___5.FStar_Interactive_JsonHelper.repl_column);
                          FStar_Interactive_JsonHelper.repl_fname =
                            (uu___5.FStar_Interactive_JsonHelper.repl_fname);
                          FStar_Interactive_JsonHelper.repl_deps_stack =
                            uu___6;
                          FStar_Interactive_JsonHelper.repl_curmod =
                            (uu___5.FStar_Interactive_JsonHelper.repl_curmod);
                          FStar_Interactive_JsonHelper.repl_env =
                            (uu___5.FStar_Interactive_JsonHelper.repl_env);
                          FStar_Interactive_JsonHelper.repl_stdin =
                            (uu___5.FStar_Interactive_JsonHelper.repl_stdin);
                          FStar_Interactive_JsonHelper.repl_names =
                            (uu___5.FStar_Interactive_JsonHelper.repl_names)
                        } in
                      aux uu___4 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2, prev::previous1) when
              let uu___ =
                FStar_Interactive_PushHelper.update_task_timestamps task in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu___
              -> (debug "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2, previous1) ->
              let uu___ = revert_many st1 previous1 in aux uu___ tasks2 [] in
        aux st tasks
          (FStar_List.rev st.FStar_Interactive_JsonHelper.repl_deps_stack)
let (js_pushkind : FStar_Util.json -> FStar_Interactive_PushHelper.push_kind)
  =
  fun s ->
    let uu___ = FStar_Interactive_JsonHelper.js_str s in
    match uu___ with
    | "syntax" -> FStar_Interactive_PushHelper.SyntaxCheck
    | "lax" -> FStar_Interactive_PushHelper.LaxCheck
    | "full" -> FStar_Interactive_PushHelper.FullCheck
    | uu___1 -> FStar_Interactive_JsonHelper.js_fail "push_kind" s
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
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
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
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
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
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
      * Prims.string Prims.list))
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
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee -> match projectee with | { qq; qid;_} -> qq
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee -> match projectee with | { qq; qid;_} -> qid
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | Exit -> false
    | DescribeProtocol -> false
    | DescribeRepl -> false
    | Segment uu___1 -> false
    | Pop -> false
    | Push
        { push_kind = uu___1; push_code = uu___2; push_line = uu___3;
          push_column = uu___4; push_peek_only = false;_}
        -> false
    | VfsAdd uu___1 -> false
    | GenericError uu___1 -> false
    | ProtocolViolation uu___1 -> false
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
  "progress"]
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
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid ->
    fun expected ->
      fun got ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Interactive_JsonHelper.json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu___2 in
          ProtocolViolation uu___1 in
        { qq = uu___; qid }
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json ->
    let assoc errloc key a =
      let uu___ = FStar_Interactive_JsonHelper.try_assoc key a in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> v
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            FStar_Interactive_JsonHelper.InvalidQuery uu___2 in
          FStar_Exn.raise uu___1 in
    let request =
      FStar_All.pipe_right json FStar_Interactive_JsonHelper.js_assoc in
    let qid =
      let uu___ = assoc "query" "query-id" request in
      FStar_All.pipe_right uu___ FStar_Interactive_JsonHelper.js_str in
    try
      (fun uu___ ->
         match () with
         | () ->
             let query1 =
               let uu___1 = assoc "query" "query" request in
               FStar_All.pipe_right uu___1
                 FStar_Interactive_JsonHelper.js_str in
             let args =
               let uu___1 = assoc "query" "args" request in
               FStar_All.pipe_right uu___1
                 FStar_Interactive_JsonHelper.js_assoc in
             let arg k = assoc "[args]" k args in
             let try_arg k =
               let uu___1 = FStar_Interactive_JsonHelper.try_assoc k args in
               match uu___1 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull) ->
                   FStar_Pervasives_Native.None
               | other -> other in
             let uu___1 =
               match query1 with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu___2 =
                     let uu___3 = arg "code" in
                     FStar_All.pipe_right uu___3
                       FStar_Interactive_JsonHelper.js_str in
                   Segment uu___2
               | "peek" ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = arg "kind" in
                       FStar_All.pipe_right uu___4 js_pushkind in
                     let uu___4 =
                       let uu___5 = arg "code" in
                       FStar_All.pipe_right uu___5
                         FStar_Interactive_JsonHelper.js_str in
                     let uu___5 =
                       let uu___6 = arg "line" in
                       FStar_All.pipe_right uu___6
                         FStar_Interactive_JsonHelper.js_int in
                     let uu___6 =
                       let uu___7 = arg "column" in
                       FStar_All.pipe_right uu___7
                         FStar_Interactive_JsonHelper.js_int in
                     {
                       push_kind = uu___3;
                       push_code = uu___4;
                       push_line = uu___5;
                       push_column = uu___6;
                       push_peek_only = (query1 = "peek")
                     } in
                   Push uu___2
               | "push" ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = arg "kind" in
                       FStar_All.pipe_right uu___4 js_pushkind in
                     let uu___4 =
                       let uu___5 = arg "code" in
                       FStar_All.pipe_right uu___5
                         FStar_Interactive_JsonHelper.js_str in
                     let uu___5 =
                       let uu___6 = arg "line" in
                       FStar_All.pipe_right uu___6
                         FStar_Interactive_JsonHelper.js_int in
                     let uu___6 =
                       let uu___7 = arg "column" in
                       FStar_All.pipe_right uu___7
                         FStar_Interactive_JsonHelper.js_int in
                     {
                       push_kind = uu___3;
                       push_code = uu___4;
                       push_line = uu___5;
                       push_column = uu___6;
                       push_peek_only = (query1 = "peek")
                     } in
                   Push uu___2
               | "autocomplete" ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = arg "partial-symbol" in
                       FStar_All.pipe_right uu___4
                         FStar_Interactive_JsonHelper.js_str in
                     let uu___4 =
                       let uu___5 = try_arg "context" in
                       FStar_All.pipe_right uu___5
                         js_optional_completion_context in
                     (uu___3, uu___4) in
                   AutoComplete uu___2
               | "lookup" ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = arg "symbol" in
                       FStar_All.pipe_right uu___4
                         FStar_Interactive_JsonHelper.js_str in
                     let uu___4 =
                       let uu___5 = try_arg "context" in
                       FStar_All.pipe_right uu___5 js_optional_lookup_context in
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = try_arg "location" in
                         FStar_All.pipe_right uu___7
                           (FStar_Util.map_option
                              FStar_Interactive_JsonHelper.js_assoc) in
                       FStar_All.pipe_right uu___6
                         (FStar_Util.map_option
                            (fun loc ->
                               let uu___7 =
                                 let uu___8 =
                                   assoc "[location]" "filename" loc in
                                 FStar_All.pipe_right uu___8
                                   FStar_Interactive_JsonHelper.js_str in
                               let uu___8 =
                                 let uu___9 = assoc "[location]" "line" loc in
                                 FStar_All.pipe_right uu___9
                                   FStar_Interactive_JsonHelper.js_int in
                               let uu___9 =
                                 let uu___10 =
                                   assoc "[location]" "column" loc in
                                 FStar_All.pipe_right uu___10
                                   FStar_Interactive_JsonHelper.js_int in
                               (uu___7, uu___8, uu___9))) in
                     let uu___6 =
                       let uu___7 = arg "requested-info" in
                       FStar_All.pipe_right uu___7
                         (FStar_Interactive_JsonHelper.js_list
                            FStar_Interactive_JsonHelper.js_str) in
                     (uu___3, uu___4, uu___5, uu___6) in
                   Lookup uu___2
               | "compute" ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = arg "term" in
                       FStar_All.pipe_right uu___4
                         FStar_Interactive_JsonHelper.js_str in
                     let uu___4 =
                       let uu___5 = try_arg "rules" in
                       FStar_All.pipe_right uu___5
                         (FStar_Util.map_option
                            (FStar_Interactive_JsonHelper.js_list
                               js_reductionrule)) in
                     (uu___3, uu___4) in
                   Compute uu___2
               | "search" ->
                   let uu___2 =
                     let uu___3 = arg "terms" in
                     FStar_All.pipe_right uu___3
                       FStar_Interactive_JsonHelper.js_str in
                   Search uu___2
               | "vfs-add" ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = try_arg "filename" in
                       FStar_All.pipe_right uu___4
                         (FStar_Util.map_option
                            FStar_Interactive_JsonHelper.js_str) in
                     let uu___4 =
                       let uu___5 = arg "contents" in
                       FStar_All.pipe_right uu___5
                         FStar_Interactive_JsonHelper.js_str in
                     (uu___3, uu___4) in
                   VfsAdd uu___2
               | uu___2 ->
                   let uu___3 =
                     FStar_Util.format1 "Unknown query '%s'" query1 in
                   ProtocolViolation uu___3 in
             { qq = uu___1; qid }) ()
    with
    | FStar_Interactive_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure qid expected got
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query ->
    try
      (fun uu___ -> match () with | () -> unpack_interactive_query js_query)
        ()
    with
    | FStar_Interactive_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid = "?" }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure "?" expected got
let (parse_interactive_query : Prims.string -> query) =
  fun query_str ->
    let uu___ = FStar_Util.json_of_string query_str in
    match uu___ with
    | FStar_Pervasives_Native.None ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream ->
    let uu___ = FStar_Util.read_line stream in
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_All.exit Prims.int_zero
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
let json_of_opt :
  'uuuuu .
    ('uuuuu -> FStar_Util.json) ->
      'uuuuu FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a ->
    fun opt_a ->
      let uu___ = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu___
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
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStar_Errors.issue_message issue in
              FStar_Util.JsonStr uu___5 in
            ("message", uu___4) in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.None -> []
                    | FStar_Pervasives_Native.Some r ->
                        let uu___9 = FStar_Range.json_of_use_range r in
                        [uu___9] in
                  let uu___9 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.Some r when
                        let uu___10 = FStar_Range.def_range r in
                        let uu___11 = FStar_Range.use_range r in
                        uu___10 <> uu___11 ->
                        let uu___10 = FStar_Range.json_of_def_range r in
                        [uu___10]
                    | uu___10 -> [] in
                  FStar_List.append uu___8 uu___9 in
                FStar_Util.JsonList uu___7 in
              ("ranges", uu___6) in
            [uu___5] in
          uu___3 :: uu___4 in
        FStar_List.append
          (match issue.FStar_Errors.issue_number with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some n ->
               [("number", (FStar_Util.JsonInt n))]) uu___2 in
      FStar_List.append
        [("level", (json_of_issue_level issue.FStar_Errors.issue_level))]
        uu___1 in
    FStar_All.pipe_left (fun uu___1 -> FStar_Util.JsonAssoc uu___1) uu___
let (alist_of_symbol_lookup_result :
  FStar_Interactive_QueryHelper.sl_reponse ->
    (Prims.string * FStar_Util.json) Prims.list)
  =
  fun lr ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          json_of_opt FStar_Range.json_of_def_range
            lr.FStar_Interactive_QueryHelper.slr_def_range in
        ("defined-at", uu___2) in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            json_of_opt (fun uu___5 -> FStar_Util.JsonStr uu___5)
              lr.FStar_Interactive_QueryHelper.slr_typ in
          ("type", uu___4) in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              json_of_opt (fun uu___7 -> FStar_Util.JsonStr uu___7)
                lr.FStar_Interactive_QueryHelper.slr_doc in
            ("documentation", uu___6) in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                json_of_opt (fun uu___9 -> FStar_Util.JsonStr uu___9)
                  lr.FStar_Interactive_QueryHelper.slr_def in
              ("definition", uu___8) in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    ("name",
      (FStar_Util.JsonStr (lr.FStar_Interactive_QueryHelper.slr_name))) ::
      uu___
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu___ =
      FStar_List.map (fun uu___1 -> FStar_Util.JsonStr uu___1)
        interactive_protocol_features in
    FStar_All.pipe_left (fun uu___1 -> FStar_Util.JsonList uu___1) uu___ in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee -> match projectee with | OptSet -> true | uu___ -> false
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReadOnly -> true | uu___ -> false
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___ -> match uu___ with | OptSet -> "" | OptReadOnly -> "read-only"
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
  fun uu___ ->
    match uu___ with
    | FStar_Options.Const uu___1 -> "flag"
    | FStar_Options.IntStr uu___1 -> "int"
    | FStar_Options.BoolStr -> "bool"
    | FStar_Options.PathStr uu___1 -> "path"
    | FStar_Options.SimpleStr uu___1 -> "string"
    | FStar_Options.EnumStr uu___1 -> "enum"
    | FStar_Options.OpenEnumStr uu___1 -> "open enum"
    | FStar_Options.PostProcessed (uu___1, typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu___1, typ) ->
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
        | FStar_Options.Const uu___ -> [""]
        | FStar_Options.BoolStr -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs, desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu___, elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu___, elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu___ = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu___
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___ ->
    match uu___ with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n -> FStar_Util.JsonInt n
    | FStar_Options.List vs ->
        let uu___1 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu___1
    | FStar_Options.Unset -> FStar_Util.JsonNull
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = json_of_fstar_option_value opt.opt_value in
          ("value", uu___3) in
        let uu___3 =
          let uu___4 =
            let uu___5 = json_of_fstar_option_value opt.opt_default in
            ("default", uu___5) in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                json_of_opt (fun uu___8 -> FStar_Util.JsonStr uu___8)
                  opt.opt_documentation in
              ("documentation", uu___7) in
            let uu___7 =
              let uu___8 =
                let uu___9 =
                  let uu___10 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu___10 in
                ("type", uu___9) in
              [uu___8;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu___6 :: uu___7 in
          uu___4 :: uu___5 in
        uu___2 :: uu___3 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu___1 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu___
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt ->
    let uu___ = alist_of_fstar_option opt in FStar_Util.JsonAssoc uu___
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
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_ST.op_Bang repl_current_qid in
              json_of_opt (fun uu___5 -> FStar_Util.JsonStr uu___5) uu___4 in
            ("query-id", uu___3) in
          [uu___2;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)] in
        ("kind", (FStar_Util.JsonStr "message")) :: uu___1 in
      FStar_Util.JsonAssoc uu___
let forward_message :
  'uuuuu .
    (FStar_Util.json -> 'uuuuu) -> Prims.string -> FStar_Util.json -> 'uuuuu
  =
  fun callback ->
    fun level ->
      fun contents ->
        let uu___ = json_of_message level contents in callback uu___
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu___ =
      FStar_List.map (fun uu___1 -> FStar_Util.JsonStr uu___1)
        interactive_protocol_features in
    FStar_Util.JsonList uu___ in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
let (write_hello : unit -> unit) =
  fun uu___ -> FStar_Interactive_JsonHelper.write_json json_of_hello
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name ->
    fun typ ->
      let flag = Prims.op_Hat "--" name in
      let uu___ = FStar_Options.desc_of_opt_type typ in
      match uu___ with
      | FStar_Pervasives_Native.None -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu___ =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu___1 ->
            match uu___1 with
            | (_shortname, name, typ, doc) ->
                let uu___2 = FStar_Util.smap_try_find defaults name in
                FStar_All.pipe_right uu___2
                  (FStar_Util.map_option
                     (fun default_value ->
                        let uu___3 = sig_of_fstar_option name typ in
                        let uu___4 = snippets_of_fstar_option name typ in
                        let uu___5 =
                          let uu___6 = FStar_Options.settable name in
                          if uu___6 then OptSet else OptReadOnly in
                        {
                          opt_name = name;
                          opt_sig = uu___3;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu___4;
                          opt_documentation =
                            (if doc = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc);
                          opt_permission_level = uu___5
                        })))) in
  FStar_All.pipe_right uu___
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
    let uu___ = opt in
    let uu___1 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___.opt_name);
      opt_sig = (uu___.opt_sig);
      opt_value = uu___1;
      opt_default = (uu___.opt_default);
      opt_type = (uu___.opt_type);
      opt_snippets = (uu___.opt_snippets);
      opt_documentation = (uu___.opt_documentation);
      opt_permission_level = (uu___.opt_permission_level)
    }
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter ->
    let uu___ = FStar_List.filter filter fstar_options_list_cache in
    FStar_List.map update_option uu___
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu___ =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu___)
    else ("", opt_name)
let (json_of_repl_state :
  FStar_Interactive_JsonHelper.repl_state -> FStar_Util.json) =
  fun st ->
    let filenames uu___ =
      match uu___ with
      | (uu___1, (task, uu___2)) ->
          (match task with
           | FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) ->
               [intf.FStar_Interactive_JsonHelper.tf_fname;
               impl.FStar_Interactive_JsonHelper.tf_fname]
           | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
               [intf_or_impl.FStar_Interactive_JsonHelper.tf_fname]
           | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
               [intf.FStar_Interactive_JsonHelper.tf_fname]
           | uu___3 -> []) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStar_List.concatMap filenames
                st.FStar_Interactive_JsonHelper.repl_deps_stack in
            FStar_List.map (fun uu___5 -> FStar_Util.JsonStr uu___5) uu___4 in
          FStar_Util.JsonList uu___3 in
        ("loaded-dependencies", uu___2) in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = current_fstar_options (fun uu___7 -> true) in
              FStar_List.map json_of_fstar_option uu___6 in
            FStar_Util.JsonList uu___5 in
          ("options", uu___4) in
        [uu___3] in
      uu___1 :: uu___2 in
    FStar_Util.JsonAssoc uu___
let run_exit :
  'uuuuu 'uuuuu1 .
    'uuuuu ->
      ((query_status * FStar_Util.json) * ('uuuuu1, Prims.int)
        FStar_Util.either)
  =
  fun st -> ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr Prims.int_zero))
let run_describe_protocol :
  'uuuuu 'uuuuu1 .
    'uuuuu ->
      ((query_status * FStar_Util.json) * ('uuuuu, 'uuuuu1)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state, 'uuuuu) FStar_Util.either)
  =
  fun st ->
    let uu___ = let uu___1 = json_of_repl_state st in (QueryOK, uu___1) in
    (uu___, (FStar_Util.Inl st))
let run_protocol_violation :
  'uuuuu 'uuuuu1 .
    'uuuuu ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('uuuuu, 'uuuuu1)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error :
  'uuuuu 'uuuuu1 .
    'uuuuu ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('uuuuu, 'uuuuu1)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu___ ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_segment :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
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
      let collect_decls uu___ =
        let uu___1 = FStar_Parser_Driver.parse_fragment frag in
        match uu___1 with
        | FStar_Parser_Driver.Empty -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module (uu___2, decls))
            -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu___2, decls, uu___3)) -> decls in
      let uu___ =
        with_captured_errors st.FStar_Interactive_JsonHelper.repl_env
          FStar_Util.sigint_ignore
          (fun uu___1 ->
             let uu___2 = collect_decls () in
             FStar_All.pipe_left
               (fun uu___3 -> FStar_Pervasives_Native.Some uu___3) uu___2) in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let errors =
            let uu___1 = collect_errors () in
            FStar_All.pipe_right uu___1 (FStar_List.map json_of_issue) in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl) in
                ("def_range", uu___3) in
              [uu___2] in
            FStar_Util.JsonAssoc uu___1 in
          let js_decls =
            let uu___1 = FStar_List.map json_of_decl decls in
            FStar_All.pipe_left (fun uu___2 -> FStar_Util.JsonList uu___2)
              uu___1 in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
let run_vfs_add :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
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
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state, 'uuuuu) FStar_Util.either)
  =
  fun st ->
    let uu___ = nothing_left_to_pop st in
    if uu___
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
      let uu___ =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents) in
      FStar_Interactive_JsonHelper.write_json uu___
let (write_repl_ld_task_progress :
  FStar_Interactive_JsonHelper.repl_task -> unit) =
  fun task ->
    match task with
    | FStar_Interactive_JsonHelper.LDInterleaved (uu___, tf) ->
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
    | uu___ -> ()
let (load_deps :
  FStar_Interactive_JsonHelper.repl_state ->
    ((FStar_Interactive_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_Interactive_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st ->
    let uu___ =
      with_captured_errors st.FStar_Interactive_JsonHelper.repl_env
        FStar_Util.sigint_ignore
        (fun _env ->
           let uu___1 =
             FStar_Interactive_PushHelper.deps_and_repl_ld_tasks_of_our_file
               st.FStar_Interactive_JsonHelper.repl_fname in
           FStar_All.pipe_left
             (fun uu___2 -> FStar_Pervasives_Native.Some uu___2) uu___1) in
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps, tasks, dep_graph) ->
        let st1 =
          let uu___1 = st in
          let uu___2 =
            FStar_TypeChecker_Env.set_dep_graph
              st.FStar_Interactive_JsonHelper.repl_env dep_graph in
          {
            FStar_Interactive_JsonHelper.repl_line =
              (uu___1.FStar_Interactive_JsonHelper.repl_line);
            FStar_Interactive_JsonHelper.repl_column =
              (uu___1.FStar_Interactive_JsonHelper.repl_column);
            FStar_Interactive_JsonHelper.repl_fname =
              (uu___1.FStar_Interactive_JsonHelper.repl_fname);
            FStar_Interactive_JsonHelper.repl_deps_stack =
              (uu___1.FStar_Interactive_JsonHelper.repl_deps_stack);
            FStar_Interactive_JsonHelper.repl_curmod =
              (uu___1.FStar_Interactive_JsonHelper.repl_curmod);
            FStar_Interactive_JsonHelper.repl_env = uu___2;
            FStar_Interactive_JsonHelper.repl_stdin =
              (uu___1.FStar_Interactive_JsonHelper.repl_stdin);
            FStar_Interactive_JsonHelper.repl_names =
              (uu___1.FStar_Interactive_JsonHelper.repl_names)
          } in
        let uu___1 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress in
        (match uu___1 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue ->
    let uu___ = issue in
    let uu___1 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_msg in
    {
      FStar_Errors.issue_msg = uu___1;
      FStar_Errors.issue_level = (uu___.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___.FStar_Errors.issue_number);
      FStar_Errors.issue_ctx = (uu___.FStar_Errors.issue_ctx)
    }
let run_push_without_deps :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
          FStar_Util.either)
  =
  fun st ->
    fun query1 ->
      let set_nosynth_flag st1 flag =
        let uu___ = st1 in
        {
          FStar_Interactive_JsonHelper.repl_line =
            (uu___.FStar_Interactive_JsonHelper.repl_line);
          FStar_Interactive_JsonHelper.repl_column =
            (uu___.FStar_Interactive_JsonHelper.repl_column);
          FStar_Interactive_JsonHelper.repl_fname =
            (uu___.FStar_Interactive_JsonHelper.repl_fname);
          FStar_Interactive_JsonHelper.repl_deps_stack =
            (uu___.FStar_Interactive_JsonHelper.repl_deps_stack);
          FStar_Interactive_JsonHelper.repl_curmod =
            (uu___.FStar_Interactive_JsonHelper.repl_curmod);
          FStar_Interactive_JsonHelper.repl_env =
            (let uu___1 = st1.FStar_Interactive_JsonHelper.repl_env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___1.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax = (uu___1.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                 (uu___1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                 (uu___1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___1.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___1.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe = (uu___1.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
               FStar_TypeChecker_Env.unif_allow_ref_guards =
                 (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards)
             });
          FStar_Interactive_JsonHelper.repl_stdin =
            (uu___.FStar_Interactive_JsonHelper.repl_stdin);
          FStar_Interactive_JsonHelper.repl_names =
            (uu___.FStar_Interactive_JsonHelper.repl_names)
        } in
      let uu___ = query1 in
      match uu___ with
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
            let uu___2 =
              run_repl_transaction st1 push_kind peek_only
                (FStar_Interactive_JsonHelper.PushFragment frag) in
            match uu___2 with
            | (success, st2) ->
                let st3 = set_nosynth_flag st2 false in
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu___3 =
                    let uu___4 = collect_errors () in
                    FStar_All.pipe_right uu___4
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu___3 in
                let st4 =
                  if success
                  then
                    let uu___3 = st3 in
                    {
                      FStar_Interactive_JsonHelper.repl_line = line;
                      FStar_Interactive_JsonHelper.repl_column = column;
                      FStar_Interactive_JsonHelper.repl_fname =
                        (uu___3.FStar_Interactive_JsonHelper.repl_fname);
                      FStar_Interactive_JsonHelper.repl_deps_stack =
                        (uu___3.FStar_Interactive_JsonHelper.repl_deps_stack);
                      FStar_Interactive_JsonHelper.repl_curmod =
                        (uu___3.FStar_Interactive_JsonHelper.repl_curmod);
                      FStar_Interactive_JsonHelper.repl_env =
                        (uu___3.FStar_Interactive_JsonHelper.repl_env);
                      FStar_Interactive_JsonHelper.repl_stdin =
                        (uu___3.FStar_Interactive_JsonHelper.repl_stdin);
                      FStar_Interactive_JsonHelper.repl_names =
                        (uu___3.FStar_Interactive_JsonHelper.repl_names)
                    }
                  else st3 in
                ((status, json_errors), (FStar_Util.Inl st4))))
let run_push_with_deps :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
          FStar_Util.either)
  =
  fun st ->
    fun query1 ->
      (let uu___1 = FStar_Options.debug_any () in
       if uu___1
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info
        st.FStar_Interactive_JsonHelper.repl_env false;
      (let uu___2 = load_deps st in
       match uu___2 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu___3 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu___3 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1, deps) ->
           ((let uu___4 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu___4 (fun uu___5 -> ()));
            (let names =
               FStar_Interactive_PushHelper.add_module_completions
                 st1.FStar_Interactive_JsonHelper.repl_fname deps
                 st1.FStar_Interactive_JsonHelper.repl_names in
             run_push_without_deps
               (let uu___4 = st1 in
                {
                  FStar_Interactive_JsonHelper.repl_line =
                    (uu___4.FStar_Interactive_JsonHelper.repl_line);
                  FStar_Interactive_JsonHelper.repl_column =
                    (uu___4.FStar_Interactive_JsonHelper.repl_column);
                  FStar_Interactive_JsonHelper.repl_fname =
                    (uu___4.FStar_Interactive_JsonHelper.repl_fname);
                  FStar_Interactive_JsonHelper.repl_deps_stack =
                    (uu___4.FStar_Interactive_JsonHelper.repl_deps_stack);
                  FStar_Interactive_JsonHelper.repl_curmod =
                    (uu___4.FStar_Interactive_JsonHelper.repl_curmod);
                  FStar_Interactive_JsonHelper.repl_env =
                    (uu___4.FStar_Interactive_JsonHelper.repl_env);
                  FStar_Interactive_JsonHelper.repl_stdin =
                    (uu___4.FStar_Interactive_JsonHelper.repl_stdin);
                  FStar_Interactive_JsonHelper.repl_names = names
                }) query1)))
let run_push :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
          FStar_Util.either)
  =
  fun st ->
    fun query1 ->
      let uu___ = nothing_left_to_pop st in
      if uu___
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
          let uu___ =
            FStar_Interactive_QueryHelper.symlookup
              st.FStar_Interactive_JsonHelper.repl_env symbol pos_opt
              requested_info in
          match uu___ with
          | FStar_Pervasives_Native.None -> FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some result ->
              let uu___1 =
                let uu___2 = alist_of_symbol_lookup_result result in
                ("symbol", uu___2) in
              FStar_Util.Inr uu___1
let (run_option_lookup :
  Prims.string ->
    (Prims.string,
      (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
      FStar_Util.either)
  =
  fun opt_name ->
    let uu___ = trim_option_name opt_name in
    match uu___ with
    | (uu___1, trimmed_name) ->
        let uu___2 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu___2 with
         | FStar_Pervasives_Native.None ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu___3 =
               let uu___4 =
                 let uu___5 = update_option opt in
                 alist_of_fstar_option uu___5 in
               ("option", uu___4) in
             FStar_Util.Inr uu___3)
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
      let uu___ =
        FStar_Interactive_CompletionTable.find_module_or_ns
          st.FStar_Interactive_JsonHelper.repl_names query1 in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu___1 =
            let uu___2 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu___2) in
          FStar_Util.Inr uu___1
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu___1 =
            let uu___2 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu___2) in
          FStar_Util.Inr uu___1
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
          let uu___ = run_symbol_lookup st symbol pos_opt requested_info in
          match uu___ with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu___1 ->
              let uu___2 = run_module_lookup st symbol in
              (match uu___2 with
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
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        lookup_context ->
          FStar_Interactive_QueryHelper.position
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) *
                (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
                FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun context ->
        fun pos_opt ->
          fun requested_info ->
            let uu___ = run_lookup' st symbol context pos_opt requested_info in
            match uu___ with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind, info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let run_code_autocomplete :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
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
  'uuuuu 'uuuuu1 'uuuuu2 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        'uuuuu ->
          'uuuuu1 ->
            ((query_status * FStar_Util.json) *
              (FStar_Interactive_JsonHelper.repl_state, 'uuuuu2)
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
              (fun uu___ -> FStar_Pervasives_Native.Some uu___) in
          let json =
            FStar_List.map
              FStar_Interactive_CompletionTable.json_of_completion_result
              mods_and_nss in
          ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let candidates_of_fstar_option :
  'uuuuu .
    Prims.int ->
      'uuuuu ->
        fstar_option ->
          FStar_Interactive_CompletionTable.completion_result Prims.list
  =
  fun match_len ->
    fun is_reset ->
      fun opt ->
        let uu___ =
          match opt.opt_permission_level with
          | OptSet -> (true, "")
          | OptReadOnly -> (false, "read-only") in
        match uu___ with
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
  'uuuuu 'uuuuu1 'uuuuu2 .
    'uuuuu ->
      Prims.string ->
        'uuuuu1 ->
          ((query_status * FStar_Util.json) * ('uuuuu, 'uuuuu2)
            FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun is_reset ->
        let uu___ = trim_option_name search_term in
        match uu___ with
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
        | (uu___1, uu___2) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
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
  'uuuuu 'uuuuu1 .
    FStar_Interactive_JsonHelper.repl_state ->
      'uuuuu ->
        (FStar_Interactive_JsonHelper.repl_state -> 'uuuuu) ->
          ('uuuuu * (FStar_Interactive_JsonHelper.repl_state, 'uuuuu1)
            FStar_Util.either)
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
            (fun uu___ ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu___1 ->
                        let uu___2 = task st1 in
                        FStar_All.pipe_left
                          (fun uu___3 -> FStar_Util.Inl uu___3) uu___2)) ()
          with | FStar_Util.SigInt -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e in
        let st2 = FStar_Interactive_PushHelper.pop_repl "run_and_rewind" st1 in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
let run_with_parsed_and_tc_term :
  'uuuuu 'uuuuu1 'uuuuu2 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        'uuuuu ->
          'uuuuu1 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) *
                (FStar_Interactive_JsonHelper.repl_state, 'uuuuu2)
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
                    ((uu___,
                      { FStar_Syntax_Syntax.lbname = uu___1;
                        FStar_Syntax_Syntax.lbunivs = univs;
                        FStar_Syntax_Syntax.lbtyp = uu___2;
                        FStar_Syntax_Syntax.lbeff = uu___3;
                        FStar_Syntax_Syntax.lbdef = def;
                        FStar_Syntax_Syntax.lbattrs = uu___4;
                        FStar_Syntax_Syntax.lbpos = uu___5;_}::[]),
                     uu___6);
                  FStar_Syntax_Syntax.sigrng = uu___7;
                  FStar_Syntax_Syntax.sigquals = uu___8;
                  FStar_Syntax_Syntax.sigmeta = uu___9;
                  FStar_Syntax_Syntax.sigattrs = uu___10;
                  FStar_Syntax_Syntax.sigopts = uu___11;_}::[] ->
                  FStar_Pervasives_Native.Some (univs, def)
              | uu___ -> FStar_Pervasives_Native.None in
            let parse frag =
              let uu___ =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag) in
              match uu___ with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls, uu___1) ->
                  FStar_Pervasives_Native.Some decls
              | uu___1 -> FStar_Pervasives_Native.None in
            let desugar env decls =
              let uu___ =
                let uu___1 = FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
                uu___1 env.FStar_TypeChecker_Env.dsenv in
              FStar_Pervasives_Native.fst uu___ in
            let typecheck tcenv decls =
              let uu___ = FStar_TypeChecker_Tc.tc_decls tcenv decls in
              match uu___ with | (ses, uu___1) -> ses in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1 ->
                 let tcenv = st1.FStar_Interactive_JsonHelper.repl_env in
                 let frag = dummy_let_fragment term in
                 let uu___ = parse frag in
                 match uu___ with
                 | FStar_Pervasives_Native.None ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu___1 =
                       let decls1 = desugar tcenv decls in
                       let ses = typecheck tcenv decls1 in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs, def) ->
                           let uu___2 =
                             FStar_Syntax_Subst.open_univ_vars univs def in
                           (match uu___2 with
                            | (univs1, def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs1 in
                                continuation tcenv1 def1) in
                     let uu___1 = FStar_Options.trace_error () in
                     if uu___1
                     then aux ()
                     else
                       (try (fun uu___3 -> match () with | () -> aux ()) ()
                        with
                        | uu___3 ->
                            let uu___4 = FStar_Errors.issue_of_exn uu___3 in
                            (match uu___4 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu___5 =
                                   let uu___6 =
                                     FStar_Errors.format_issue issue in
                                   FStar_Util.JsonStr uu___6 in
                                 (QueryNOK, uu___5)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Exn.raise uu___3)))
let run_compute :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
            FStar_Util.either)
  =
  fun st ->
    fun term ->
      fun rules ->
        let rules1 =
          FStar_List.append
            (match rules with
             | FStar_Pervasives_Native.Some rules2 -> rules2
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
               let uu___ =
                 let uu___1 =
                   FStar_Interactive_QueryHelper.term_to_string tcenv
                     normalized in
                 FStar_Util.JsonStr uu___1 in
               (QueryOK, uu___))
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NameContainsStr _0 -> true | uu___ -> false
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee -> match projectee with | NameContainsStr _0 -> _0
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeContainsLid _0 -> true | uu___ -> false
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TypeContainsLid _0 -> _0
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | { st_negate; st_term;_} -> st_negate
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee -> match projectee with | { st_negate; st_term;_} -> st_term
let (st_cost : search_term' -> Prims.int) =
  fun uu___ ->
    match uu___ with
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
    let uu___ = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu___1 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu___; sc_fvars = uu___1 }
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv ->
    fun sc ->
      let uu___ = FStar_ST.op_Bang sc.sc_typ in
      match uu___ with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let typ =
            let uu___1 = FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu___1 with
            | FStar_Pervasives_Native.None ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu___2, typ1), uu___3) -> typ1 in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
let (sc_fvars :
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lident FStar_Util.set)
  =
  fun tcenv ->
    fun sc ->
      let uu___ = FStar_ST.op_Bang sc.sc_fvars in
      match uu___ with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None ->
          let fv =
            let uu___1 = sc_typ tcenv sc in FStar_Syntax_Free.fvars uu___1 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv ->
    fun sc ->
      let typ_str =
        let uu___ = sc_typ tcenv sc in
        FStar_Interactive_QueryHelper.term_to_string tcenv uu___ in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              FStar_Ident.string_of_lid uu___4 in
            FStar_Util.JsonStr uu___3 in
          ("lid", uu___2) in
        [uu___1; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu___
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidSearch uu___ -> true | uu___ -> false
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | InvalidSearch uu___ -> uu___
let run_search :
  'uuuuu .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state, 'uuuuu)
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
              let uu___ = FStar_Ident.string_of_lid candidate.sc_lid in
              FStar_Util.contains uu___ str
          | TypeContainsLid lid ->
              let uu___ = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu___ in
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
              let uu___ =
                let uu___1 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu___1 in
              FStar_Exn.raise uu___
            else
              if beg_quote
              then
                (let uu___1 = strip_quotes term1 in NameContainsStr uu___1)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu___2 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu___2 with
                 | FStar_Pervasives_Native.None ->
                     let uu___3 =
                       let uu___4 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu___4 in
                     FStar_Exn.raise uu___3
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu___ =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l ->
              let uu___1 = FStar_Ident.string_of_lid l in
              FStar_Util.format1 "%s" uu___1 in
        Prims.op_Hat (if term.st_negate then "-" else "") uu___ in
      let results =
        try
          (fun uu___ ->
             match () with
             | () ->
                 let terms = parse search_str in
                 let all_lidents = FStar_TypeChecker_Env.lidents tcenv in
                 let all_candidates = FStar_List.map sc_of_lid all_lidents in
                 let matches_all candidate =
                   FStar_List.for_all (st_matches candidate) terms in
                 let cmp r1 r2 =
                   let uu___1 = FStar_Ident.string_of_lid r1.sc_lid in
                   let uu___2 = FStar_Ident.string_of_lid r2.sc_lid in
                   FStar_Util.compare uu___1 uu___2 in
                 let results1 = FStar_List.filter matches_all all_candidates in
                 let sorted = FStar_Util.sort_with cmp results1 in
                 let js = FStar_List.map (json_of_search_result tcenv) sorted in
                 (match results1 with
                  | [] ->
                      let kwds =
                        let uu___1 = FStar_List.map pprint_one terms in
                        FStar_Util.concat_l " " uu___1 in
                      let uu___1 =
                        let uu___2 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds in
                        InvalidSearch uu___2 in
                      FStar_Exn.raise uu___1
                  | uu___1 -> (QueryOK, (FStar_Util.JsonList js)))) ()
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
            push_code = uu___; push_line = uu___1; push_column = uu___2;
            push_peek_only = false;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu___ ->
          (match st.FStar_Interactive_JsonHelper.repl_curmod with
           | FStar_Pervasives_Native.None when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu___1 -> q)
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
      let uu___ = validate_and_run_query st query1 in
      match uu___ with
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
      let uu___ = deserialize_interactive_query query_js in
      js_repl_eval st uu___
let (js_repl_eval_str :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string * (FStar_Interactive_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query_str ->
      let uu___ =
        let uu___1 = parse_interactive_query query_str in
        js_repl_eval st uu___1 in
      match uu___ with
      | (js_response, st_opt) ->
          let uu___1 = FStar_Util.string_of_json js_response in
          (uu___1, st_opt)
let (js_repl_init_opts : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStar_Options.parse_cmd_line () in
    match uu___1 with
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
              | h::uu___2::uu___3 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu___2 -> ()))
let rec (go : FStar_Interactive_JsonHelper.repl_state -> Prims.int) =
  fun st ->
    let query1 =
      read_interactive_query st.FStar_Interactive_JsonHelper.repl_stdin in
    let uu___ = validate_and_run_query st query1 in
    match uu___ with
    | ((status, response), state_opt) ->
        (write_response query1.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref [] in
  let add_one e =
    let uu___ = let uu___1 = FStar_ST.op_Bang issues in e :: uu___1 in
    FStar_ST.op_Colon_Equals issues uu___ in
  let count_errors uu___ =
    let issues1 =
      let uu___1 = FStar_ST.op_Bang issues in
      FStar_Util.remove_dups (fun i0 -> fun i1 -> i0 = i1) uu___1 in
    let uu___1 =
      FStar_List.filter
        (fun e -> e.FStar_Errors.issue_level = FStar_Errors.EError) issues1 in
    FStar_List.length uu___1 in
  let report uu___ =
    let uu___1 =
      let uu___2 = FStar_ST.op_Bang issues in
      FStar_Util.remove_dups (fun i0 -> fun i1 -> i0 = i1) uu___2 in
    FStar_List.sortWith FStar_Errors.compare_issues uu___1 in
  let clear uu___ = FStar_ST.op_Colon_Equals issues [] in
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
               let uu___ = get_json () in forward_message printer label uu___)
    }
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
let (initial_range : FStar_Range.range) =
  let uu___ = FStar_Range.mk_pos Prims.int_one Prims.int_zero in
  let uu___1 = FStar_Range.mk_pos Prims.int_one Prims.int_zero in
  FStar_Range.mk_range "<input>" uu___ uu___1
let (build_initial_repl_state :
  Prims.string -> FStar_Interactive_JsonHelper.repl_state) =
  fun filename ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range in
    let uu___ = FStar_Util.open_stdin () in
    {
      FStar_Interactive_JsonHelper.repl_line = Prims.int_one;
      FStar_Interactive_JsonHelper.repl_column = Prims.int_zero;
      FStar_Interactive_JsonHelper.repl_fname = filename;
      FStar_Interactive_JsonHelper.repl_deps_stack = [];
      FStar_Interactive_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_Interactive_JsonHelper.repl_env = env1;
      FStar_Interactive_JsonHelper.repl_stdin = uu___;
      FStar_Interactive_JsonHelper.repl_names =
        FStar_Interactive_CompletionTable.empty
    }
let interactive_mode' :
  'uuuuu . FStar_Interactive_JsonHelper.repl_state -> 'uuuuu =
  fun init_st ->
    write_hello ();
    (let exit_code =
       let uu___1 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu___1
       then
         let uu___2 =
           let uu___3 = FStar_Options.file_list () in FStar_List.hd uu___3 in
         FStar_SMTEncoding_Solver.with_hints_db uu___2
           (fun uu___3 -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let (interactive_mode : Prims.string -> unit) =
  fun filename ->
    install_ide_mode_hooks FStar_Interactive_JsonHelper.write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu___3 =
       let uu___4 = FStar_Options.codegen () in FStar_Option.isSome uu___4 in
     if uu___3
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init = build_initial_repl_state filename in
     let uu___3 = FStar_Options.trace_error () in
     if uu___3
     then interactive_mode' init
     else
       (try (fun uu___5 -> match () with | () -> interactive_mode' init) ()
        with
        | uu___5 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___5)))