open Prims
let with_captured_errors' :
  'uuuuuu28 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'uuuuuu28 FStar_Pervasives_Native.option)
          -> 'uuuuuu28 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        try
          (fun uu___11_58  ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu____64  -> f env)) ()
        with
        | FStar_All.Failure msg ->
            let msg1 =
              Prims.op_Hat "ASSERTION FAILURE: "
                (Prims.op_Hat msg
                   (Prims.op_Hat "\n"
                      (Prims.op_Hat "F* may be in an inconsistent state.\n"
                         (Prims.op_Hat
                            "Please file a bug report, ideally with a "
                            "minimized version of the program that triggered the error."))))
               in
            ((let uu____82 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.log_issue uu____82
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt  ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e,msg,r) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e,msg) ->
            ((let uu____112 =
                let uu____122 =
                  let uu____130 = FStar_TypeChecker_Env.get_range env  in
                  (e, msg, uu____130)  in
                [uu____122]  in
              FStar_TypeChecker_Err.add_errors env uu____112);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop  -> FStar_Pervasives_Native.None
  
let with_captured_errors :
  'uuuuuu155 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'uuuuuu155 FStar_Pervasives_Native.option)
          -> 'uuuuuu155 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        let uu____182 = FStar_Options.trace_error ()  in
        if uu____182
        then f env
        else with_captured_errors' env sigint_handler f
  
let (t0 : FStar_Util.time) = FStar_Util.now () 
let (dummy_tf_of_fname :
  Prims.string -> FStar_Interactive_JsonHelper.timed_fname) =
  fun fname  ->
    {
      FStar_Interactive_JsonHelper.tf_fname = fname;
      FStar_Interactive_JsonHelper.tf_modtime = t0
    }
  
let (string_of_timed_fname :
  FStar_Interactive_JsonHelper.timed_fname -> Prims.string) =
  fun uu____204  ->
    match uu____204 with
    | { FStar_Interactive_JsonHelper.tf_fname = fname;
        FStar_Interactive_JsonHelper.tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____214 = FStar_Util.string_of_time modtime  in
           FStar_Util.format2 "{ %s; %s }" fname uu____214)
  
type push_query =
  {
  push_kind: FStar_Interactive_PushHelper.push_kind ;
  push_code: Prims.string ;
  push_line: Prims.int ;
  push_column: Prims.int ;
  push_peek_only: Prims.bool }
let (__proj__Mkpush_query__item__push_kind :
  push_query -> FStar_Interactive_PushHelper.push_kind) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_kind
  
let (__proj__Mkpush_query__item__push_code : push_query -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_code
  
let (__proj__Mkpush_query__item__push_line : push_query -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_line
  
let (__proj__Mkpush_query__item__push_column : push_query -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_column
  
let (__proj__Mkpush_query__item__push_peek_only : push_query -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_peek_only
  
type env_t = FStar_TypeChecker_Env.env
let (repl_current_qid :
  Prims.string FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (nothing_left_to_pop :
  FStar_Interactive_JsonHelper.repl_state -> Prims.bool) =
  fun st  ->
    let uu____346 =
      let uu____347 =
        FStar_ST.op_Bang FStar_Interactive_PushHelper.repl_stack  in
      FStar_List.length uu____347  in
    uu____346 =
      (FStar_List.length st.FStar_Interactive_JsonHelper.repl_deps_stack)
  
let (string_of_repl_task :
  FStar_Interactive_JsonHelper.repl_task -> Prims.string) =
  fun uu___0_399  ->
    match uu___0_399 with
    | FStar_Interactive_JsonHelper.LDInterleaved (intf,impl) ->
        let uu____403 = string_of_timed_fname intf  in
        let uu____405 = string_of_timed_fname impl  in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____403 uu____405
    | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
        let uu____409 = string_of_timed_fname intf_or_impl  in
        FStar_Util.format1 "LDSingle %s" uu____409
    | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu____413 = string_of_timed_fname intf  in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____413
    | FStar_Interactive_JsonHelper.PushFragment frag ->
        FStar_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
    | FStar_Interactive_JsonHelper.Noop  -> "Noop {}"
  
let (run_repl_transaction :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Interactive_PushHelper.push_kind ->
      Prims.bool ->
        FStar_Interactive_JsonHelper.repl_task ->
          (Prims.bool * FStar_Interactive_JsonHelper.repl_state))
  =
  fun st  ->
    fun push_kind  ->
      fun must_rollback  ->
        fun task  ->
          let st1 =
            FStar_Interactive_PushHelper.push_repl "run_repl_transaction"
              push_kind task st
             in
          let uu____449 =
            FStar_Interactive_PushHelper.track_name_changes
              st1.FStar_Interactive_JsonHelper.repl_env
             in
          match uu____449 with
          | (env,finish_name_tracking) ->
              let check_success uu____494 =
                (let uu____497 = FStar_Errors.get_err_count ()  in
                 uu____497 = Prims.int_zero) &&
                  (Prims.op_Negation must_rollback)
                 in
              let uu____501 =
                let uu____509 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1  ->
                       let uu____523 =
                         FStar_Interactive_PushHelper.run_repl_task
                           st1.FStar_Interactive_JsonHelper.repl_curmod env1
                           task
                          in
                       FStar_All.pipe_left
                         (fun uu____542  ->
                            FStar_Pervasives_Native.Some uu____542) uu____523)
                   in
                match uu____509 with
                | FStar_Pervasives_Native.Some (curmod,env1) when
                    check_success () -> (curmod, env1, true)
                | uu____558 ->
                    ((st1.FStar_Interactive_JsonHelper.repl_curmod), env,
                      false)
                 in
              (match uu____501 with
               | (curmod,env1,success) ->
                   let uu____577 = finish_name_tracking env1  in
                   (match uu____577 with
                    | (env2,name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___95_598 = st1  in
                              {
                                FStar_Interactive_JsonHelper.repl_line =
                                  (uu___95_598.FStar_Interactive_JsonHelper.repl_line);
                                FStar_Interactive_JsonHelper.repl_column =
                                  (uu___95_598.FStar_Interactive_JsonHelper.repl_column);
                                FStar_Interactive_JsonHelper.repl_fname =
                                  (uu___95_598.FStar_Interactive_JsonHelper.repl_fname);
                                FStar_Interactive_JsonHelper.repl_deps_stack
                                  =
                                  (uu___95_598.FStar_Interactive_JsonHelper.repl_deps_stack);
                                FStar_Interactive_JsonHelper.repl_curmod =
                                  curmod;
                                FStar_Interactive_JsonHelper.repl_env = env2;
                                FStar_Interactive_JsonHelper.repl_stdin =
                                  (uu___95_598.FStar_Interactive_JsonHelper.repl_stdin);
                                FStar_Interactive_JsonHelper.repl_names =
                                  (uu___95_598.FStar_Interactive_JsonHelper.repl_names)
                              }  in
                            FStar_Interactive_PushHelper.commit_name_tracking
                              st2 name_events
                          else
                            FStar_Interactive_PushHelper.pop_repl
                              "run_repl_transaction" st1
                           in
                        (success, st2)))
  
let (run_repl_ld_transactions :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Interactive_JsonHelper.repl_task Prims.list ->
      (FStar_Interactive_JsonHelper.repl_task -> unit) ->
        (FStar_Interactive_JsonHelper.repl_state,FStar_Interactive_JsonHelper.repl_state)
          FStar_Util.either)
  =
  fun st  ->
    fun tasks  ->
      fun progress_callback  ->
        let debug verb task =
          let uu____645 = FStar_Options.debug_any ()  in
          if uu____645
          then
            let uu____648 = string_of_repl_task task  in
            FStar_Util.print2 "%s %s" verb uu____648
          else ()  in
        let rec revert_many st1 uu___1_673 =
          match uu___1_673 with
          | [] -> st1
          | (_id,(task,_st'))::entries ->
              (debug "Reverting" task;
               (let st' =
                  FStar_Interactive_PushHelper.pop_repl
                    "run_repl_ls_transactions" st1
                   in
                let dep_graph =
                  FStar_TypeChecker_Env.dep_graph
                    st1.FStar_Interactive_JsonHelper.repl_env
                   in
                let st'1 =
                  let uu___121_726 = st'  in
                  let uu____727 =
                    FStar_TypeChecker_Env.set_dep_graph
                      st'.FStar_Interactive_JsonHelper.repl_env dep_graph
                     in
                  {
                    FStar_Interactive_JsonHelper.repl_line =
                      (uu___121_726.FStar_Interactive_JsonHelper.repl_line);
                    FStar_Interactive_JsonHelper.repl_column =
                      (uu___121_726.FStar_Interactive_JsonHelper.repl_column);
                    FStar_Interactive_JsonHelper.repl_fname =
                      (uu___121_726.FStar_Interactive_JsonHelper.repl_fname);
                    FStar_Interactive_JsonHelper.repl_deps_stack =
                      (uu___121_726.FStar_Interactive_JsonHelper.repl_deps_stack);
                    FStar_Interactive_JsonHelper.repl_curmod =
                      (uu___121_726.FStar_Interactive_JsonHelper.repl_curmod);
                    FStar_Interactive_JsonHelper.repl_env = uu____727;
                    FStar_Interactive_JsonHelper.repl_stdin =
                      (uu___121_726.FStar_Interactive_JsonHelper.repl_stdin);
                    FStar_Interactive_JsonHelper.repl_names =
                      (uu___121_726.FStar_Interactive_JsonHelper.repl_names)
                  }  in
                revert_many st'1 entries))
           in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([],[]) -> FStar_Util.Inl st1
          | (task::tasks2,[]) ->
              (debug "Loading" task;
               progress_callback task;
               (let uu____780 = FStar_Options.restore_cmd_line_options false
                   in
                FStar_All.pipe_right uu____780 (fun uu____782  -> ()));
               (let timestamped_task =
                  FStar_Interactive_PushHelper.update_task_timestamps task
                   in
                let push_kind =
                  let uu____785 = FStar_Options.lax ()  in
                  if uu____785
                  then FStar_Interactive_PushHelper.LaxCheck
                  else FStar_Interactive_PushHelper.FullCheck  in
                let uu____790 =
                  run_repl_transaction st1 push_kind false timestamped_task
                   in
                match uu____790 with
                | (success,st2) ->
                    if success
                    then
                      let uu____810 =
                        let uu___146_811 = st2  in
                        let uu____812 =
                          FStar_ST.op_Bang
                            FStar_Interactive_PushHelper.repl_stack
                           in
                        {
                          FStar_Interactive_JsonHelper.repl_line =
                            (uu___146_811.FStar_Interactive_JsonHelper.repl_line);
                          FStar_Interactive_JsonHelper.repl_column =
                            (uu___146_811.FStar_Interactive_JsonHelper.repl_column);
                          FStar_Interactive_JsonHelper.repl_fname =
                            (uu___146_811.FStar_Interactive_JsonHelper.repl_fname);
                          FStar_Interactive_JsonHelper.repl_deps_stack =
                            uu____812;
                          FStar_Interactive_JsonHelper.repl_curmod =
                            (uu___146_811.FStar_Interactive_JsonHelper.repl_curmod);
                          FStar_Interactive_JsonHelper.repl_env =
                            (uu___146_811.FStar_Interactive_JsonHelper.repl_env);
                          FStar_Interactive_JsonHelper.repl_stdin =
                            (uu___146_811.FStar_Interactive_JsonHelper.repl_stdin);
                          FStar_Interactive_JsonHelper.repl_names =
                            (uu___146_811.FStar_Interactive_JsonHelper.repl_names)
                        }  in
                      aux uu____810 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2,prev::previous1) when
              let uu____856 =
                FStar_Interactive_PushHelper.update_task_timestamps task  in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____856
              -> (debug "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2,previous1) ->
              let uu____873 = revert_many st1 previous1  in
              aux uu____873 tasks2 []
           in
        aux st tasks
          (FStar_List.rev st.FStar_Interactive_JsonHelper.repl_deps_stack)
  
let (js_pushkind : FStar_Util.json -> FStar_Interactive_PushHelper.push_kind)
  =
  fun s  ->
    let uu____888 = FStar_Interactive_JsonHelper.js_str s  in
    match uu____888 with
    | "syntax" -> FStar_Interactive_PushHelper.SyntaxCheck
    | "lax" -> FStar_Interactive_PushHelper.LaxCheck
    | "full" -> FStar_Interactive_PushHelper.FullCheck
    | uu____893 -> FStar_Interactive_JsonHelper.js_fail "push_kind" s
  
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s  ->
    let uu____902 = FStar_Interactive_JsonHelper.js_str s  in
    match uu____902 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____910 -> FStar_Interactive_JsonHelper.js_fail "reduction rule" s
  
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____939 -> false
  
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____952 -> false
  
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee  -> match projectee with | CKOption _0 -> _0 
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____980 -> false
  
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0 
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1018 = FStar_Interactive_JsonHelper.js_str k1  in
        (match uu____1018 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____1046 ->
             FStar_Interactive_JsonHelper.js_fail
               "completion context (code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
  
type lookup_context =
  | LKSymbolOnly 
  | LKModule 
  | LKOption 
  | LKCode 
let (uu___is_LKSymbolOnly : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKSymbolOnly  -> true | uu____1058 -> false
  
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____1069 -> false
  
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____1080 -> false
  
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____1091 -> false
  
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1104 = FStar_Interactive_JsonHelper.js_str k1  in
        (match uu____1104 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____1114 ->
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
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1231 -> false
  
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1242 -> false
  
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1253 -> false
  
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____1266 -> false
  
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Segment _0 -> _0 
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1287 -> false 
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1299 -> false
  
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____1326 -> false
  
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee  -> match projectee with | VfsAdd _0 -> _0 
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1374 -> false
  
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0 
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____1422 -> false
  
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee  -> match projectee with | Lookup _0 -> _0 
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____1492 -> false
  
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Compute _0 -> _0 
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____1539 -> false
  
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Search _0 -> _0 
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____1562 -> false
  
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | GenericError _0 -> _0 
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____1585 -> false
  
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0 
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee  -> match projectee with | { qq; qid;_} -> qq 
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee  -> match projectee with | { qq; qid;_} -> qid 
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___2_1623  ->
    match uu___2_1623 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____1628 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____1632; push_code = uu____1633;
          push_line = uu____1634; push_column = uu____1635;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____1641 -> false
    | GenericError uu____1651 -> false
    | ProtocolViolation uu____1654 -> false
    | Push uu____1657 -> true
    | AutoComplete uu____1659 -> true
    | Lookup uu____1666 -> true
    | Compute uu____1682 -> true
    | Search uu____1693 -> true
  
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
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____1755 -> false
  
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____1766 -> false
  
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____1777 -> false
  
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____1799 =
          let uu____1800 =
            let uu____1802 = FStar_Interactive_JsonHelper.json_debug got  in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1802
             in
          ProtocolViolation uu____1800  in
        { qq = uu____1799; qid }
  
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json  ->
    let assoc errloc key a =
      let uu____1831 = FStar_Interactive_JsonHelper.try_assoc key a  in
      match uu____1831 with
      | FStar_Pervasives_Native.Some v -> v
      | FStar_Pervasives_Native.None  ->
          let uu____1835 =
            let uu____1836 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc  in
            FStar_Interactive_JsonHelper.InvalidQuery uu____1836  in
          FStar_Exn.raise uu____1835
       in
    let request =
      FStar_All.pipe_right json FStar_Interactive_JsonHelper.js_assoc  in
    let qid =
      let uu____1842 = assoc "query" "query-id" request  in
      FStar_All.pipe_right uu____1842 FStar_Interactive_JsonHelper.js_str  in
    try
      (fun uu___259_1852  ->
         match () with
         | () ->
             let query1 =
               let uu____1855 = assoc "query" "query" request  in
               FStar_All.pipe_right uu____1855
                 FStar_Interactive_JsonHelper.js_str
                in
             let args =
               let uu____1860 = assoc "query" "args" request  in
               FStar_All.pipe_right uu____1860
                 FStar_Interactive_JsonHelper.js_assoc
                in
             let arg k = assoc "[args]" k args  in
             let try_arg k =
               let uu____1882 = FStar_Interactive_JsonHelper.try_assoc k args
                  in
               match uu____1882 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
                   FStar_Pervasives_Native.None
               | other -> other  in
             let uu____1890 =
               match query1 with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____1896 =
                     let uu____1898 = arg "code"  in
                     FStar_All.pipe_right uu____1898
                       FStar_Interactive_JsonHelper.js_str
                      in
                   Segment uu____1896
               | "peek" ->
                   let uu____1902 =
                     let uu____1903 =
                       let uu____1904 = arg "kind"  in
                       FStar_All.pipe_right uu____1904 js_pushkind  in
                     let uu____1906 =
                       let uu____1908 = arg "code"  in
                       FStar_All.pipe_right uu____1908
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____1911 =
                       let uu____1913 = arg "line"  in
                       FStar_All.pipe_right uu____1913
                         FStar_Interactive_JsonHelper.js_int
                        in
                     let uu____1916 =
                       let uu____1918 = arg "column"  in
                       FStar_All.pipe_right uu____1918
                         FStar_Interactive_JsonHelper.js_int
                        in
                     {
                       push_kind = uu____1903;
                       push_code = uu____1906;
                       push_line = uu____1911;
                       push_column = uu____1916;
                       push_peek_only = (query1 = "peek")
                     }  in
                   Push uu____1902
               | "push" ->
                   let uu____1924 =
                     let uu____1925 =
                       let uu____1926 = arg "kind"  in
                       FStar_All.pipe_right uu____1926 js_pushkind  in
                     let uu____1928 =
                       let uu____1930 = arg "code"  in
                       FStar_All.pipe_right uu____1930
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____1933 =
                       let uu____1935 = arg "line"  in
                       FStar_All.pipe_right uu____1935
                         FStar_Interactive_JsonHelper.js_int
                        in
                     let uu____1938 =
                       let uu____1940 = arg "column"  in
                       FStar_All.pipe_right uu____1940
                         FStar_Interactive_JsonHelper.js_int
                        in
                     {
                       push_kind = uu____1925;
                       push_code = uu____1928;
                       push_line = uu____1933;
                       push_column = uu____1938;
                       push_peek_only = (query1 = "peek")
                     }  in
                   Push uu____1924
               | "autocomplete" ->
                   let uu____1946 =
                     let uu____1952 =
                       let uu____1954 = arg "partial-symbol"  in
                       FStar_All.pipe_right uu____1954
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____1957 =
                       let uu____1958 = try_arg "context"  in
                       FStar_All.pipe_right uu____1958
                         js_optional_completion_context
                        in
                     (uu____1952, uu____1957)  in
                   AutoComplete uu____1946
               | "lookup" ->
                   let uu____1966 =
                     let uu____1981 =
                       let uu____1983 = arg "symbol"  in
                       FStar_All.pipe_right uu____1983
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____1986 =
                       let uu____1987 = try_arg "context"  in
                       FStar_All.pipe_right uu____1987
                         js_optional_lookup_context
                        in
                     let uu____1993 =
                       let uu____1996 =
                         let uu____1999 = try_arg "location"  in
                         FStar_All.pipe_right uu____1999
                           (FStar_Util.map_option
                              FStar_Interactive_JsonHelper.js_assoc)
                          in
                       FStar_All.pipe_right uu____1996
                         (FStar_Util.map_option
                            (fun loc  ->
                               let uu____2025 =
                                 let uu____2027 =
                                   assoc "[location]" "filename" loc  in
                                 FStar_All.pipe_right uu____2027
                                   FStar_Interactive_JsonHelper.js_str
                                  in
                               let uu____2031 =
                                 let uu____2033 =
                                   assoc "[location]" "line" loc  in
                                 FStar_All.pipe_right uu____2033
                                   FStar_Interactive_JsonHelper.js_int
                                  in
                               let uu____2037 =
                                 let uu____2039 =
                                   assoc "[location]" "column" loc  in
                                 FStar_All.pipe_right uu____2039
                                   FStar_Interactive_JsonHelper.js_int
                                  in
                               (uu____2025, uu____2031, uu____2037)))
                        in
                     let uu____2046 =
                       let uu____2050 = arg "requested-info"  in
                       FStar_All.pipe_right uu____2050
                         (FStar_Interactive_JsonHelper.js_list
                            FStar_Interactive_JsonHelper.js_str)
                        in
                     (uu____1981, uu____1986, uu____1993, uu____2046)  in
                   Lookup uu____1966
               | "compute" ->
                   let uu____2063 =
                     let uu____2073 =
                       let uu____2075 = arg "term"  in
                       FStar_All.pipe_right uu____2075
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____2078 =
                       let uu____2083 = try_arg "rules"  in
                       FStar_All.pipe_right uu____2083
                         (FStar_Util.map_option
                            (FStar_Interactive_JsonHelper.js_list
                               js_reductionrule))
                        in
                     (uu____2073, uu____2078)  in
                   Compute uu____2063
               | "search" ->
                   let uu____2101 =
                     let uu____2103 = arg "terms"  in
                     FStar_All.pipe_right uu____2103
                       FStar_Interactive_JsonHelper.js_str
                      in
                   Search uu____2101
               | "vfs-add" ->
                   let uu____2107 =
                     let uu____2116 =
                       let uu____2120 = try_arg "filename"  in
                       FStar_All.pipe_right uu____2120
                         (FStar_Util.map_option
                            FStar_Interactive_JsonHelper.js_str)
                        in
                     let uu____2130 =
                       let uu____2132 = arg "contents"  in
                       FStar_All.pipe_right uu____2132
                         FStar_Interactive_JsonHelper.js_str
                        in
                     (uu____2116, uu____2130)  in
                   VfsAdd uu____2107
               | uu____2139 ->
                   let uu____2141 =
                     FStar_Util.format1 "Unknown query '%s'" query1  in
                   ProtocolViolation uu____2141
                in
             { qq = uu____1890; qid }) ()
    with
    | FStar_Interactive_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected,got) ->
        wrap_js_failure qid expected got
  
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query  ->
    try
      (fun uu___294_2160  ->
         match () with | () -> unpack_interactive_query js_query) ()
    with
    | FStar_Interactive_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid = "?" }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected,got) ->
        wrap_js_failure "?" expected got
  
let (parse_interactive_query : Prims.string -> query) =
  fun query_str  ->
    let uu____2180 = FStar_Util.json_of_string query_str  in
    match uu____2180 with
    | FStar_Pervasives_Native.None  ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
  
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream  ->
    let uu____2192 = FStar_Util.read_line stream  in
    match uu____2192 with
    | FStar_Pervasives_Native.None  -> FStar_All.exit Prims.int_zero
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
  
let json_of_opt :
  'uuuuuu2208 .
    ('uuuuuu2208 -> FStar_Util.json) ->
      'uuuuuu2208 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2228 = FStar_Util.map_option json_of_a opt_a  in
      FStar_Util.dflt FStar_Util.JsonNull uu____2228
  
let (json_of_issue_level : FStar_Errors.issue_level -> FStar_Util.json) =
  fun i  ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented  -> "not-implemented"
       | FStar_Errors.EInfo  -> "info"
       | FStar_Errors.EWarning  -> "warning"
       | FStar_Errors.EError  -> "error")
  
let (json_of_issue : FStar_Errors.issue -> FStar_Util.json) =
  fun issue  ->
    let uu____2248 =
      let uu____2256 =
        let uu____2264 =
          let uu____2272 =
            let uu____2280 =
              let uu____2286 =
                let uu____2287 =
                  let uu____2290 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.None  -> []
                    | FStar_Pervasives_Native.Some r ->
                        let uu____2296 = FStar_Range.json_of_use_range r  in
                        [uu____2296]
                     in
                  let uu____2297 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.Some r when
                        let uu____2303 = FStar_Range.def_range r  in
                        let uu____2304 = FStar_Range.use_range r  in
                        uu____2303 <> uu____2304 ->
                        let uu____2305 = FStar_Range.json_of_def_range r  in
                        [uu____2305]
                    | uu____2306 -> []  in
                  FStar_List.append uu____2290 uu____2297  in
                FStar_Util.JsonList uu____2287  in
              ("ranges", uu____2286)  in
            [uu____2280]  in
          ("message",
            (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))) ::
            uu____2272
           in
        FStar_List.append
          (match issue.FStar_Errors.issue_number with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some n ->
               [("number", (FStar_Util.JsonInt n))]) uu____2264
         in
      FStar_List.append
        [("level", (json_of_issue_level issue.FStar_Errors.issue_level))]
        uu____2256
       in
    FStar_All.pipe_left (fun uu____2385  -> FStar_Util.JsonAssoc uu____2385)
      uu____2248
  
let (alist_of_symbol_lookup_result :
  FStar_Interactive_QueryHelper.sl_reponse ->
    (Prims.string * FStar_Util.json) Prims.list)
  =
  fun lr  ->
    let uu____2399 =
      let uu____2407 =
        let uu____2413 =
          json_of_opt FStar_Range.json_of_def_range
            lr.FStar_Interactive_QueryHelper.slr_def_range
           in
        ("defined-at", uu____2413)  in
      let uu____2416 =
        let uu____2424 =
          let uu____2430 =
            json_of_opt (fun uu____2432  -> FStar_Util.JsonStr uu____2432)
              lr.FStar_Interactive_QueryHelper.slr_typ
             in
          ("type", uu____2430)  in
        let uu____2435 =
          let uu____2443 =
            let uu____2449 =
              json_of_opt (fun uu____2451  -> FStar_Util.JsonStr uu____2451)
                lr.FStar_Interactive_QueryHelper.slr_doc
               in
            ("documentation", uu____2449)  in
          let uu____2454 =
            let uu____2462 =
              let uu____2468 =
                json_of_opt
                  (fun uu____2470  -> FStar_Util.JsonStr uu____2470)
                  lr.FStar_Interactive_QueryHelper.slr_def
                 in
              ("definition", uu____2468)  in
            [uu____2462]  in
          uu____2443 :: uu____2454  in
        uu____2424 :: uu____2435  in
      uu____2407 :: uu____2416  in
    ("name",
      (FStar_Util.JsonStr (lr.FStar_Interactive_QueryHelper.slr_name))) ::
      uu____2399
  
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____2515 =
      FStar_List.map (fun uu____2519  -> FStar_Util.JsonStr uu____2519)
        interactive_protocol_features
       in
    FStar_All.pipe_left (fun uu____2522  -> FStar_Util.JsonList uu____2522)
      uu____2515
     in
  [("version", js_version); ("features", js_features)] 
type fstar_option_permission_level =
  | OptSet 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____2551 -> false
  
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____2562 -> false
  
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___3_2570  ->
    match uu___3_2570 with | OptSet  -> "" | OptReadOnly  -> "read-only"
  
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
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_name
  
let (__proj__Mkfstar_option__item__opt_sig : fstar_option -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_sig
  
let (__proj__Mkfstar_option__item__opt_value :
  fstar_option -> FStar_Options.option_val) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_value
  
let (__proj__Mkfstar_option__item__opt_default :
  fstar_option -> FStar_Options.option_val) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_default
  
let (__proj__Mkfstar_option__item__opt_type :
  fstar_option -> FStar_Options.opt_type) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_type
  
let (__proj__Mkfstar_option__item__opt_snippets :
  fstar_option -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_snippets
  
let (__proj__Mkfstar_option__item__opt_documentation :
  fstar_option -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_documentation
  
let (__proj__Mkfstar_option__item__opt_permission_level :
  fstar_option -> fstar_option_permission_level) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_permission_level
  
let rec (kind_of_fstar_option_type : FStar_Options.opt_type -> Prims.string)
  =
  fun uu___4_2820  ->
    match uu___4_2820 with
    | FStar_Options.Const uu____2822 -> "flag"
    | FStar_Options.IntStr uu____2824 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____2828 -> "path"
    | FStar_Options.SimpleStr uu____2831 -> "string"
    | FStar_Options.EnumStr uu____2834 -> "enum"
    | FStar_Options.OpenEnumStr uu____2839 -> "open enum"
    | FStar_Options.PostProcessed (uu____2849,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____2859,typ) ->
        kind_of_fstar_option_type typ
  
let (snippets_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string Prims.list) =
  fun name  ->
    fun typ  ->
      let mk_field field_name =
        Prims.op_Hat "${" (Prims.op_Hat field_name "}")  in
      let mk_snippet name1 argstring =
        Prims.op_Hat "--"
          (Prims.op_Hat name1
             (if argstring <> "" then Prims.op_Hat " " argstring else ""))
         in
      let rec arg_snippets_of_type typ1 =
        match typ1 with
        | FStar_Options.Const uu____2931 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____2969,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____2979,elem_spec) ->
            arg_snippets_of_type elem_spec
         in
      let uu____2987 = arg_snippets_of_type typ  in
      FStar_List.map (mk_snippet name) uu____2987
  
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___5_2998  ->
    match uu___5_2998 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n -> FStar_Util.JsonInt n
    | FStar_Options.List vs ->
        let uu____3010 = FStar_List.map json_of_fstar_option_value vs  in
        FStar_Util.JsonList uu____3010
    | FStar_Options.Unset  -> FStar_Util.JsonNull
  
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt  ->
    let uu____3026 =
      let uu____3034 =
        let uu____3042 =
          let uu____3048 = json_of_fstar_option_value opt.opt_value  in
          ("value", uu____3048)  in
        let uu____3051 =
          let uu____3059 =
            let uu____3065 = json_of_fstar_option_value opt.opt_default  in
            ("default", uu____3065)  in
          let uu____3068 =
            let uu____3076 =
              let uu____3082 =
                json_of_opt
                  (fun uu____3084  -> FStar_Util.JsonStr uu____3084)
                  opt.opt_documentation
                 in
              ("documentation", uu____3082)  in
            let uu____3087 =
              let uu____3095 =
                let uu____3101 =
                  let uu____3102 = kind_of_fstar_option_type opt.opt_type  in
                  FStar_Util.JsonStr uu____3102  in
                ("type", uu____3101)  in
              [uu____3095;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))]
               in
            uu____3076 :: uu____3087  in
          uu____3059 :: uu____3068  in
        uu____3042 :: uu____3051  in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____3034  in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3026
  
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt  ->
    let uu____3158 = alist_of_fstar_option opt  in
    FStar_Util.JsonAssoc uu____3158
  
let (json_of_response :
  Prims.string -> query_status -> FStar_Util.json -> FStar_Util.json) =
  fun qid  ->
    fun status  ->
      fun response  ->
        let qid1 = FStar_Util.JsonStr qid  in
        let status1 =
          match status with
          | QueryOK  -> FStar_Util.JsonStr "success"
          | QueryNOK  -> FStar_Util.JsonStr "failure"
          | QueryViolatesProtocol  -> FStar_Util.JsonStr "protocol-violation"
           in
        FStar_Util.JsonAssoc
          [("kind", (FStar_Util.JsonStr "response"));
          ("query-id", qid1);
          ("status", status1);
          ("response", response)]
  
let (write_response :
  Prims.string -> query_status -> FStar_Util.json -> unit) =
  fun qid  ->
    fun status  ->
      fun response  ->
        FStar_Interactive_JsonHelper.write_json
          (json_of_response qid status response)
  
let (json_of_message : Prims.string -> FStar_Util.json -> FStar_Util.json) =
  fun level  ->
    fun js_contents  ->
      let uu____3254 =
        let uu____3262 =
          let uu____3270 =
            let uu____3276 =
              let uu____3277 = FStar_ST.op_Bang repl_current_qid  in
              json_of_opt (fun uu____3307  -> FStar_Util.JsonStr uu____3307)
                uu____3277
               in
            ("query-id", uu____3276)  in
          [uu____3270;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)]  in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____3262  in
      FStar_Util.JsonAssoc uu____3254
  
let forward_message :
  'uuuuuu3351 .
    (FStar_Util.json -> 'uuuuuu3351) ->
      Prims.string -> FStar_Util.json -> 'uuuuuu3351
  =
  fun callback  ->
    fun level  ->
      fun contents  ->
        let uu____3374 = json_of_message level contents  in
        callback uu____3374
  
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____3378 =
      FStar_List.map (fun uu____3382  -> FStar_Util.JsonStr uu____3382)
        interactive_protocol_features
       in
    FStar_Util.JsonList uu____3378  in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
  
let (write_hello : unit -> unit) =
  fun uu____3396  -> FStar_Interactive_JsonHelper.write_json json_of_hello 
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name  ->
    fun typ  ->
      let flag = Prims.op_Hat "--" name  in
      let uu____3414 = FStar_Options.desc_of_opt_type typ  in
      match uu____3414 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
  
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults = FStar_Util.smap_of_list FStar_Options.defaults  in
  let uu____3430 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____3465  ->
            match uu____3465 with
            | (_shortname,name,typ,doc) ->
                let uu____3489 = FStar_Util.smap_try_find defaults name  in
                FStar_All.pipe_right uu____3489
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____3501 = sig_of_fstar_option name typ  in
                        let uu____3503 = snippets_of_fstar_option name typ
                           in
                        let uu____3507 =
                          let uu____3508 = FStar_Options.settable name  in
                          if uu____3508 then OptSet else OptReadOnly  in
                        {
                          opt_name = name;
                          opt_sig = uu____3501;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____3503;
                          opt_documentation =
                            (if doc = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc);
                          opt_permission_level = uu____3507
                        }))))
     in
  FStar_All.pipe_right uu____3430
    (FStar_List.sortWith
       (fun o1  ->
          fun o2  ->
            FStar_String.compare (FStar_String.lowercase o1.opt_name)
              (FStar_String.lowercase o2.opt_name)))
  
let (fstar_options_map_cache : fstar_option FStar_Util.smap) =
  let cache = FStar_Util.smap_create (Prims.of_int (50))  in
  FStar_List.iter (fun opt  -> FStar_Util.smap_add cache opt.opt_name opt)
    fstar_options_list_cache;
  cache 
let (update_option : fstar_option -> fstar_option) =
  fun opt  ->
    let uu___467_3547 = opt  in
    let uu____3548 = FStar_Options.get_option opt.opt_name  in
    {
      opt_name = (uu___467_3547.opt_name);
      opt_sig = (uu___467_3547.opt_sig);
      opt_value = uu____3548;
      opt_default = (uu___467_3547.opt_default);
      opt_type = (uu___467_3547.opt_type);
      opt_snippets = (uu___467_3547.opt_snippets);
      opt_documentation = (uu___467_3547.opt_documentation);
      opt_permission_level = (uu___467_3547.opt_permission_level)
    }
  
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter  ->
    let uu____3564 = FStar_List.filter filter fstar_options_list_cache  in
    FStar_List.map update_option uu____3564
  
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name  ->
    let opt_prefix = "--"  in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____3591 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix)
         in
      (opt_prefix, uu____3591)
    else ("", opt_name)
  
let (json_of_repl_state :
  FStar_Interactive_JsonHelper.repl_state -> FStar_Util.json) =
  fun st  ->
    let filenames uu____3622 =
      match uu____3622 with
      | (uu____3634,(task,uu____3636)) ->
          (match task with
           | FStar_Interactive_JsonHelper.LDInterleaved (intf,impl) ->
               [intf.FStar_Interactive_JsonHelper.tf_fname;
               impl.FStar_Interactive_JsonHelper.tf_fname]
           | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
               [intf_or_impl.FStar_Interactive_JsonHelper.tf_fname]
           | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
               [intf.FStar_Interactive_JsonHelper.tf_fname]
           | uu____3655 -> [])
       in
    let uu____3657 =
      let uu____3665 =
        let uu____3671 =
          let uu____3672 =
            let uu____3675 =
              FStar_List.concatMap filenames
                st.FStar_Interactive_JsonHelper.repl_deps_stack
               in
            FStar_List.map (fun uu____3689  -> FStar_Util.JsonStr uu____3689)
              uu____3675
             in
          FStar_Util.JsonList uu____3672  in
        ("loaded-dependencies", uu____3671)  in
      let uu____3692 =
        let uu____3700 =
          let uu____3706 =
            let uu____3707 =
              let uu____3710 =
                current_fstar_options (fun uu____3715  -> true)  in
              FStar_List.map json_of_fstar_option uu____3710  in
            FStar_Util.JsonList uu____3707  in
          ("options", uu____3706)  in
        [uu____3700]  in
      uu____3665 :: uu____3692  in
    FStar_Util.JsonAssoc uu____3657
  
let run_exit :
  'uuuuuu3741 'uuuuuu3742 .
    'uuuuuu3741 ->
      ((query_status * FStar_Util.json) * ('uuuuuu3742,Prims.int)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr Prims.int_zero))
  
let run_describe_protocol :
  'uuuuuu3779 'uuuuuu3780 .
    'uuuuuu3779 ->
      ((query_status * FStar_Util.json) * ('uuuuuu3779,'uuuuuu3780)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
  
let run_describe_repl :
  'uuuuuu3811 .
    FStar_Interactive_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state,'uuuuuu3811)
        FStar_Util.either)
  =
  fun st  ->
    let uu____3829 =
      let uu____3834 = json_of_repl_state st  in (QueryOK, uu____3834)  in
    (uu____3829, (FStar_Util.Inl st))
  
let run_protocol_violation :
  'uuuuuu3852 'uuuuuu3853 .
    'uuuuuu3852 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('uuuuuu3852,'uuuuuu3853)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
  
let run_generic_error :
  'uuuuuu3895 'uuuuuu3896 .
    'uuuuuu3895 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('uuuuuu3895,'uuuuuu3896)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
  
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____3936  ->
    let errors = FStar_Errors.report_all ()  in FStar_Errors.clear (); errors
  
let run_segment :
  'uuuuuu3948 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'uuuuuu3948)
          FStar_Util.either)
  =
  fun st  ->
    fun code  ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_fname = "<input>";
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = Prims.int_one;
          FStar_Parser_ParseIt.frag_col = Prims.int_zero
        }  in
      let collect_decls uu____3984 =
        let uu____3985 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____3985 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____3991,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____3997,decls,uu____3999)) -> decls
         in
      let uu____4006 =
        with_captured_errors st.FStar_Interactive_JsonHelper.repl_env
          FStar_Util.sigint_ignore
          (fun uu____4015  ->
             let uu____4016 = collect_decls ()  in
             FStar_All.pipe_left
               (fun uu____4027  -> FStar_Pervasives_Native.Some uu____4027)
               uu____4016)
         in
      match uu____4006 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____4045 = collect_errors ()  in
            FStar_All.pipe_right uu____4045 (FStar_List.map json_of_issue)
             in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____4071 =
              let uu____4079 =
                let uu____4085 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl)
                   in
                ("def_range", uu____4085)  in
              [uu____4079]  in
            FStar_Util.JsonAssoc uu____4071  in
          let js_decls =
            let uu____4099 = FStar_List.map json_of_decl decls  in
            FStar_All.pipe_left
              (fun uu____4104  -> FStar_Util.JsonList uu____4104) uu____4099
             in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
  
let run_vfs_add :
  'uuuuuu4134 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state,'uuuuuu4134)
            FStar_Util.either)
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname =
          FStar_Util.dflt st.FStar_Interactive_JsonHelper.repl_fname
            opt_fname
           in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
  
let run_pop :
  'uuuuuu4187 .
    FStar_Interactive_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state,'uuuuuu4187)
        FStar_Util.either)
  =
  fun st  ->
    let uu____4205 = nothing_left_to_pop st  in
    if uu____4205
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let st' = FStar_Interactive_PushHelper.pop_repl "pop_query" st  in
       ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))
  
let (write_progress :
  Prims.string FStar_Pervasives_Native.option ->
    (Prims.string * FStar_Util.json) Prims.list -> unit)
  =
  fun stage  ->
    fun contents_alist  ->
      let stage1 =
        match stage with
        | FStar_Pervasives_Native.Some s -> FStar_Util.JsonStr s
        | FStar_Pervasives_Native.None  -> FStar_Util.JsonNull  in
      let js_contents = ("stage", stage1) :: contents_alist  in
      let uu____4292 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents)  in
      FStar_Interactive_JsonHelper.write_json uu____4292
  
let (write_repl_ld_task_progress :
  FStar_Interactive_JsonHelper.repl_task -> unit) =
  fun task  ->
    match task with
    | FStar_Interactive_JsonHelper.LDInterleaved (uu____4300,tf) ->
        let modname =
          FStar_Parser_Dep.module_name_of_file
            tf.FStar_Interactive_JsonHelper.tf_fname
           in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | FStar_Interactive_JsonHelper.LDSingle tf ->
        let modname =
          FStar_Parser_Dep.module_name_of_file
            tf.FStar_Interactive_JsonHelper.tf_fname
           in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile tf ->
        let modname =
          FStar_Parser_Dep.module_name_of_file
            tf.FStar_Interactive_JsonHelper.tf_fname
           in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | uu____4352 -> ()
  
let (load_deps :
  FStar_Interactive_JsonHelper.repl_state ->
    ((FStar_Interactive_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_Interactive_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st  ->
    let uu____4370 =
      with_captured_errors st.FStar_Interactive_JsonHelper.repl_env
        FStar_Util.sigint_ignore
        (fun _env  ->
           let uu____4398 =
             FStar_Interactive_PushHelper.deps_and_repl_ld_tasks_of_our_file
               st.FStar_Interactive_JsonHelper.repl_fname
              in
           FStar_All.pipe_left
             (fun uu____4445  -> FStar_Pervasives_Native.Some uu____4445)
             uu____4398)
       in
    match uu____4370 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph) ->
        let st1 =
          let uu___557_4500 = st  in
          let uu____4501 =
            FStar_TypeChecker_Env.set_dep_graph
              st.FStar_Interactive_JsonHelper.repl_env dep_graph
             in
          {
            FStar_Interactive_JsonHelper.repl_line =
              (uu___557_4500.FStar_Interactive_JsonHelper.repl_line);
            FStar_Interactive_JsonHelper.repl_column =
              (uu___557_4500.FStar_Interactive_JsonHelper.repl_column);
            FStar_Interactive_JsonHelper.repl_fname =
              (uu___557_4500.FStar_Interactive_JsonHelper.repl_fname);
            FStar_Interactive_JsonHelper.repl_deps_stack =
              (uu___557_4500.FStar_Interactive_JsonHelper.repl_deps_stack);
            FStar_Interactive_JsonHelper.repl_curmod =
              (uu___557_4500.FStar_Interactive_JsonHelper.repl_curmod);
            FStar_Interactive_JsonHelper.repl_env = uu____4501;
            FStar_Interactive_JsonHelper.repl_stdin =
              (uu___557_4500.FStar_Interactive_JsonHelper.repl_stdin);
            FStar_Interactive_JsonHelper.repl_names =
              (uu___557_4500.FStar_Interactive_JsonHelper.repl_names)
          }  in
        let uu____4502 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress  in
        (match uu____4502 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
  
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue  ->
    let uu___567_4557 = issue  in
    let uu____4558 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message
       in
    {
      FStar_Errors.issue_message = uu____4558;
      FStar_Errors.issue_level = (uu___567_4557.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___567_4557.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___567_4557.FStar_Errors.issue_number)
    }
  
let run_push_without_deps :
  'uuuuuu4568 .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'uuuuuu4568)
          FStar_Util.either)
  =
  fun st  ->
    fun query1  ->
      let set_nosynth_flag st1 flag =
        let uu___574_4604 = st1  in
        {
          FStar_Interactive_JsonHelper.repl_line =
            (uu___574_4604.FStar_Interactive_JsonHelper.repl_line);
          FStar_Interactive_JsonHelper.repl_column =
            (uu___574_4604.FStar_Interactive_JsonHelper.repl_column);
          FStar_Interactive_JsonHelper.repl_fname =
            (uu___574_4604.FStar_Interactive_JsonHelper.repl_fname);
          FStar_Interactive_JsonHelper.repl_deps_stack =
            (uu___574_4604.FStar_Interactive_JsonHelper.repl_deps_stack);
          FStar_Interactive_JsonHelper.repl_curmod =
            (uu___574_4604.FStar_Interactive_JsonHelper.repl_curmod);
          FStar_Interactive_JsonHelper.repl_env =
            (let uu___576_4606 = st1.FStar_Interactive_JsonHelper.repl_env
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___576_4606.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___576_4606.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___576_4606.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___576_4606.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___576_4606.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___576_4606.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___576_4606.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___576_4606.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___576_4606.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___576_4606.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___576_4606.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___576_4606.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___576_4606.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___576_4606.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___576_4606.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___576_4606.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___576_4606.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___576_4606.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___576_4606.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___576_4606.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___576_4606.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___576_4606.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___576_4606.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___576_4606.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___576_4606.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___576_4606.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___576_4606.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___576_4606.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___576_4606.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___576_4606.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___576_4606.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___576_4606.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___576_4606.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___576_4606.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___576_4606.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___576_4606.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___576_4606.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___576_4606.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___576_4606.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___576_4606.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___576_4606.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___576_4606.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___576_4606.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___576_4606.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___576_4606.FStar_TypeChecker_Env.erasable_types_tab)
             });
          FStar_Interactive_JsonHelper.repl_stdin =
            (uu___574_4604.FStar_Interactive_JsonHelper.repl_stdin);
          FStar_Interactive_JsonHelper.repl_names =
            (uu___574_4604.FStar_Interactive_JsonHelper.repl_names)
        }  in
      let uu____4607 = query1  in
      match uu____4607 with
      | { push_kind; push_code = text; push_line = line;
          push_column = column; push_peek_only = peek_only;_} ->
          let frag =
            {
              FStar_Parser_ParseIt.frag_fname = "<input>";
              FStar_Parser_ParseIt.frag_text = text;
              FStar_Parser_ParseIt.frag_line = line;
              FStar_Parser_ParseIt.frag_col = column
            }  in
          (FStar_TypeChecker_Env.toggle_id_info
             st.FStar_Interactive_JsonHelper.repl_env true;
           (let st1 = set_nosynth_flag st peek_only  in
            let uu____4634 =
              run_repl_transaction st1 push_kind peek_only
                (FStar_Interactive_JsonHelper.PushFragment frag)
               in
            match uu____4634 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false  in
                let status =
                  if success || peek_only then QueryOK else QueryNOK  in
                let json_errors =
                  let uu____4663 =
                    let uu____4666 = collect_errors ()  in
                    FStar_All.pipe_right uu____4666
                      (FStar_List.map json_of_issue)
                     in
                  FStar_Util.JsonList uu____4663  in
                let st4 =
                  if success
                  then
                    let uu___595_4675 = st3  in
                    {
                      FStar_Interactive_JsonHelper.repl_line = line;
                      FStar_Interactive_JsonHelper.repl_column = column;
                      FStar_Interactive_JsonHelper.repl_fname =
                        (uu___595_4675.FStar_Interactive_JsonHelper.repl_fname);
                      FStar_Interactive_JsonHelper.repl_deps_stack =
                        (uu___595_4675.FStar_Interactive_JsonHelper.repl_deps_stack);
                      FStar_Interactive_JsonHelper.repl_curmod =
                        (uu___595_4675.FStar_Interactive_JsonHelper.repl_curmod);
                      FStar_Interactive_JsonHelper.repl_env =
                        (uu___595_4675.FStar_Interactive_JsonHelper.repl_env);
                      FStar_Interactive_JsonHelper.repl_stdin =
                        (uu___595_4675.FStar_Interactive_JsonHelper.repl_stdin);
                      FStar_Interactive_JsonHelper.repl_names =
                        (uu___595_4675.FStar_Interactive_JsonHelper.repl_names)
                    }
                  else st3  in
                ((status, json_errors), (FStar_Util.Inl st4))))
  
let run_push_with_deps :
  'uuuuuu4693 .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'uuuuuu4693)
          FStar_Util.either)
  =
  fun st  ->
    fun query1  ->
      (let uu____4717 = FStar_Options.debug_any ()  in
       if uu____4717
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info
        st.FStar_Interactive_JsonHelper.repl_env false;
      (let uu____4725 = load_deps st  in
       match uu____4725 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____4760 = collect_errors ()  in
             FStar_List.map rephrase_dependency_error uu____4760  in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue)  in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____4794 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____4794 (fun uu____4796  -> ()));
            (let names =
               FStar_Interactive_PushHelper.add_module_completions
                 st1.FStar_Interactive_JsonHelper.repl_fname deps
                 st1.FStar_Interactive_JsonHelper.repl_names
                in
             run_push_without_deps
               (let uu___613_4799 = st1  in
                {
                  FStar_Interactive_JsonHelper.repl_line =
                    (uu___613_4799.FStar_Interactive_JsonHelper.repl_line);
                  FStar_Interactive_JsonHelper.repl_column =
                    (uu___613_4799.FStar_Interactive_JsonHelper.repl_column);
                  FStar_Interactive_JsonHelper.repl_fname =
                    (uu___613_4799.FStar_Interactive_JsonHelper.repl_fname);
                  FStar_Interactive_JsonHelper.repl_deps_stack =
                    (uu___613_4799.FStar_Interactive_JsonHelper.repl_deps_stack);
                  FStar_Interactive_JsonHelper.repl_curmod =
                    (uu___613_4799.FStar_Interactive_JsonHelper.repl_curmod);
                  FStar_Interactive_JsonHelper.repl_env =
                    (uu___613_4799.FStar_Interactive_JsonHelper.repl_env);
                  FStar_Interactive_JsonHelper.repl_stdin =
                    (uu___613_4799.FStar_Interactive_JsonHelper.repl_stdin);
                  FStar_Interactive_JsonHelper.repl_names = names
                }) query1)))
  
let run_push :
  'uuuuuu4807 .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'uuuuuu4807)
          FStar_Util.either)
  =
  fun st  ->
    fun query1  ->
      let uu____4830 = nothing_left_to_pop st  in
      if uu____4830
      then run_push_with_deps st query1
      else run_push_without_deps st query1
  
let (run_symbol_lookup :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      FStar_Interactive_QueryHelper.position FStar_Pervasives_Native.option
        ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                          Prims.list))
            FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____4897 =
            FStar_Interactive_QueryHelper.symlookup
              st.FStar_Interactive_JsonHelper.repl_env symbol pos_opt
              requested_info
             in
          match uu____4897 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some result ->
              let uu____4932 =
                let uu____4945 = alist_of_symbol_lookup_result result  in
                ("symbol", uu____4945)  in
              FStar_Util.Inr uu____4932
  
let (run_option_lookup :
  Prims.string ->
    (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                    Prims.list))
      FStar_Util.either)
  =
  fun opt_name  ->
    let uu____5000 = trim_option_name opt_name  in
    match uu____5000 with
    | (uu____5024,trimmed_name) ->
        let uu____5030 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name  in
        (match uu____5030 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____5065 =
               let uu____5078 =
                 let uu____5086 = update_option opt  in
                 alist_of_fstar_option uu____5086  in
               ("option", uu____5078)  in
             FStar_Util.Inr uu____5065)
  
let (run_module_lookup :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                      Prims.list))
        FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      let query1 = FStar_Util.split symbol "."  in
      let uu____5144 =
        FStar_Interactive_CompletionTable.find_module_or_ns
          st.FStar_Interactive_JsonHelper.repl_names query1
         in
      match uu____5144 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____5179 =
            let uu____5192 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info
               in
            ("module", uu____5192)  in
          FStar_Util.Inr uu____5179
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____5223 =
            let uu____5236 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info  in
            ("namespace", uu____5236)  in
          FStar_Util.Inr uu____5223
  
let (run_code_lookup :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      FStar_Interactive_QueryHelper.position FStar_Pervasives_Native.option
        ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                          Prims.list))
            FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____5316 = run_symbol_lookup st symbol pos_opt requested_info
             in
          match uu____5316 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____5390 ->
              let uu____5405 = run_module_lookup st symbol  in
              (match uu____5405 with
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
            (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                            Prims.list))
              FStar_Util.either)
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
  
let run_lookup :
  'uuuuuu5593 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        lookup_context ->
          FStar_Interactive_QueryHelper.position
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) *
                (FStar_Interactive_JsonHelper.repl_state,'uuuuuu5593)
                FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____5643 =
              run_lookup' st symbol context pos_opt requested_info  in
            match uu____5643 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
  
let run_code_autocomplete :
  'uuuuuu5749 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'uuuuuu5749)
          FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      let result = FStar_Interactive_QueryHelper.ck_completion st search_term
         in
      let js =
        FStar_List.map
          FStar_Interactive_CompletionTable.json_of_completion_result result
         in
      ((QueryOK, (FStar_Util.JsonList js)), (FStar_Util.Inl st))
  
let run_module_autocomplete :
  'uuuuuu5803 'uuuuuu5804 'uuuuuu5805 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        'uuuuuu5803 ->
          'uuuuuu5804 ->
            ((query_status * FStar_Util.json) *
              (FStar_Interactive_JsonHelper.repl_state,'uuuuuu5805)
              FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun modules  ->
        fun namespaces  ->
          let needle = FStar_Util.split search_term "."  in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.FStar_Interactive_JsonHelper.repl_names needle
              (fun uu____5852  -> FStar_Pervasives_Native.Some uu____5852)
             in
          let json =
            FStar_List.map
              FStar_Interactive_CompletionTable.json_of_completion_result
              mods_and_nss
             in
          ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
  
let candidates_of_fstar_option :
  'uuuuuu5873 .
    Prims.int ->
      'uuuuuu5873 ->
        fstar_option ->
          FStar_Interactive_CompletionTable.completion_result Prims.list
  =
  fun match_len  ->
    fun is_reset  ->
      fun opt  ->
        let uu____5893 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReadOnly  -> (false, "read-only")  in
        match uu____5893 with
        | (may_set,explanation) ->
            let opt_type = kind_of_fstar_option_type opt.opt_type  in
            let annot =
              if may_set
              then opt_type
              else
                Prims.op_Hat "("
                  (Prims.op_Hat explanation
                     (Prims.op_Hat " " (Prims.op_Hat opt_type ")")))
               in
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
  
let run_option_autocomplete :
  'uuuuuu5955 'uuuuuu5956 'uuuuuu5957 .
    'uuuuuu5955 ->
      Prims.string ->
        'uuuuuu5956 ->
          ((query_status * FStar_Util.json) * ('uuuuuu5955,'uuuuuu5957)
            FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____5987 = trim_option_name search_term  in
        match uu____5987 with
        | ("--",trimmed_name) ->
            let matcher opt =
              FStar_Util.starts_with opt.opt_name trimmed_name  in
            let options = current_fstar_options matcher  in
            let match_len = FStar_String.length search_term  in
            let collect_candidates =
              candidates_of_fstar_option match_len is_reset  in
            let results = FStar_List.concatMap collect_candidates options  in
            let json =
              FStar_List.map
                FStar_Interactive_CompletionTable.json_of_completion_result
                results
               in
            ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
        | (uu____6043,uu____6044) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
  
let run_autocomplete :
  'uuuuuu6067 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state,'uuuuuu6067)
            FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun context  ->
        match context with
        | CKCode  -> run_code_autocomplete st search_term
        | CKOption is_reset ->
            run_option_autocomplete st search_term is_reset
        | CKModuleOrNamespace (modules,namespaces) ->
            run_module_autocomplete st search_term modules namespaces
  
let run_and_rewind :
  'uuuuuu6119 'uuuuuu6120 .
    FStar_Interactive_JsonHelper.repl_state ->
      'uuuuuu6119 ->
        (FStar_Interactive_JsonHelper.repl_state -> 'uuuuuu6119) ->
          ('uuuuuu6119 *
            (FStar_Interactive_JsonHelper.repl_state,'uuuuuu6120)
            FStar_Util.either)
  =
  fun st  ->
    fun sigint_default  ->
      fun task  ->
        let st1 =
          FStar_Interactive_PushHelper.push_repl "run_and_rewind"
            FStar_Interactive_PushHelper.FullCheck
            FStar_Interactive_JsonHelper.Noop st
           in
        let results =
          try
            (fun uu___728_6161  ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____6172  ->
                        let uu____6173 = task st1  in
                        FStar_All.pipe_left
                          (fun uu____6178  -> FStar_Util.Inl uu____6178)
                          uu____6173)) ()
          with | FStar_Util.SigInt  -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e  in
        let st2 = FStar_Interactive_PushHelper.pop_repl "run_and_rewind" st1
           in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
  
let run_with_parsed_and_tc_term :
  'uuuuuu6227 'uuuuuu6228 'uuuuuu6229 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        'uuuuuu6227 ->
          'uuuuuu6228 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) *
                (FStar_Interactive_JsonHelper.repl_state,'uuuuuu6229)
                FStar_Util.either)
  =
  fun st  ->
    fun term  ->
      fun line  ->
        fun column  ->
          fun continuation  ->
            let dummy_let_fragment term1 =
              let dummy_decl =
                FStar_Util.format1 "let __compute_dummy__ = (%s)" term1  in
              {
                FStar_Parser_ParseIt.frag_fname = "<input>";
                FStar_Parser_ParseIt.frag_text = dummy_decl;
                FStar_Parser_ParseIt.frag_line = Prims.int_zero;
                FStar_Parser_ParseIt.frag_col = Prims.int_zero
              }  in
            let find_let_body ses =
              match ses with
              | {
                  FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                    ((uu____6331,{ FStar_Syntax_Syntax.lbname = uu____6332;
                                   FStar_Syntax_Syntax.lbunivs = univs;
                                   FStar_Syntax_Syntax.lbtyp = uu____6334;
                                   FStar_Syntax_Syntax.lbeff = uu____6335;
                                   FStar_Syntax_Syntax.lbdef = def;
                                   FStar_Syntax_Syntax.lbattrs = uu____6337;
                                   FStar_Syntax_Syntax.lbpos = uu____6338;_}::[]),uu____6339);
                  FStar_Syntax_Syntax.sigrng = uu____6340;
                  FStar_Syntax_Syntax.sigquals = uu____6341;
                  FStar_Syntax_Syntax.sigmeta = uu____6342;
                  FStar_Syntax_Syntax.sigattrs = uu____6343;
                  FStar_Syntax_Syntax.sigopts = uu____6344;_}::[] ->
                  FStar_Pervasives_Native.Some (univs, def)
              | uu____6385 -> FStar_Pervasives_Native.None  in
            let parse frag =
              let uu____6406 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag)
                 in
              match uu____6406 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____6412) ->
                  FStar_Pervasives_Native.Some decls
              | uu____6433 -> FStar_Pervasives_Native.None  in
            let desugar env decls =
              let uu____6451 =
                let uu____6456 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls  in
                uu____6456 env.FStar_TypeChecker_Env.dsenv  in
              FStar_Pervasives_Native.fst uu____6451  in
            let typecheck tcenv decls =
              let uu____6478 = FStar_TypeChecker_Tc.tc_decls tcenv decls  in
              match uu____6478 with | (ses,uu____6492,uu____6493) -> ses  in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1  ->
                 let tcenv = st1.FStar_Interactive_JsonHelper.repl_env  in
                 let frag = dummy_let_fragment term  in
                 let uu____6514 = parse frag  in
                 match uu____6514 with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____6540 =
                       let decls1 = desugar tcenv decls  in
                       let ses = typecheck tcenv decls1  in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs,def) ->
                           let uu____6576 =
                             FStar_Syntax_Subst.open_univ_vars univs def  in
                           (match uu____6576 with
                            | (univs1,def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs1
                                   in
                                continuation tcenv1 def1)
                        in
                     let uu____6588 = FStar_Options.trace_error ()  in
                     if uu____6588
                     then aux ()
                     else
                       (try
                          (fun uu___812_6602  -> match () with | () -> aux ())
                            ()
                        with
                        | uu___811_6611 ->
                            let uu____6616 =
                              FStar_Errors.issue_of_exn uu___811_6611  in
                            (match uu____6616 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____6624 =
                                   let uu____6625 =
                                     FStar_Errors.format_issue issue  in
                                   FStar_Util.JsonStr uu____6625  in
                                 (QueryNOK, uu____6624)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Exn.raise uu___811_6611)))
  
let run_compute :
  'uuuuuu6640 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state,'uuuuuu6640)
            FStar_Util.either)
  =
  fun st  ->
    fun term  ->
      fun rules  ->
        let rules1 =
          FStar_List.append
            (match rules with
             | FStar_Pervasives_Native.Some rules1 -> rules1
             | FStar_Pervasives_Native.None  ->
                 [FStar_TypeChecker_Env.Beta;
                 FStar_TypeChecker_Env.Iota;
                 FStar_TypeChecker_Env.Zeta;
                 FStar_TypeChecker_Env.UnfoldUntil
                   FStar_Syntax_Syntax.delta_constant])
            [FStar_TypeChecker_Env.Inlining;
            FStar_TypeChecker_Env.Eager_unfolding;
            FStar_TypeChecker_Env.UnfoldTac;
            FStar_TypeChecker_Env.Primops]
           in
        let normalize_term tcenv rules2 t =
          FStar_TypeChecker_Normalize.normalize rules2 tcenv t  in
        run_with_parsed_and_tc_term st term Prims.int_zero Prims.int_zero
          (fun tcenv  ->
             fun def  ->
               let normalized = normalize_term tcenv rules1 def  in
               let uu____6718 =
                 let uu____6719 =
                   FStar_Interactive_QueryHelper.term_to_string tcenv
                     normalized
                    in
                 FStar_Util.JsonStr uu____6719  in
               (QueryOK, uu____6718))
  
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____6754 -> false
  
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0 
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____6776 -> false
  
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0 
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | { st_negate; st_term;_} -> st_negate
  
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee  -> match projectee with | { st_negate; st_term;_} -> st_term 
let (st_cost : search_term' -> Prims.int) =
  fun uu___6_6811  ->
    match uu___6_6811 with
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
  fun projectee  ->
    match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_lid
  
let (__proj__Mksearch_candidate__item__sc_typ :
  search_candidate ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_typ
  
let (__proj__Mksearch_candidate__item__sc_fvars :
  search_candidate ->
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_fvars
  
let (sc_of_lid : FStar_Ident.lid -> search_candidate) =
  fun lid  ->
    let uu____6997 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    let uu____7004 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    { sc_lid = lid; sc_typ = uu____6997; sc_fvars = uu____7004 }
  
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv  ->
    fun sc  ->
      let uu____7028 = FStar_ST.op_Bang sc.sc_typ  in
      match uu____7028 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____7056 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid  in
            match uu____7056 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7075,typ),uu____7077) ->
                typ
             in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
  
let (sc_fvars :
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lident FStar_Util.set)
  =
  fun tcenv  ->
    fun sc  ->
      let uu____7127 = FStar_ST.op_Bang sc.sc_fvars  in
      match uu____7127 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____7171 = sc_typ tcenv sc  in
            FStar_Syntax_Free.fvars uu____7171  in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
  
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____7215 = sc_typ tcenv sc  in
        FStar_Interactive_QueryHelper.term_to_string tcenv uu____7215  in
      let uu____7216 =
        let uu____7224 =
          let uu____7230 =
            let uu____7231 =
              let uu____7233 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid
                 in
              FStar_Ident.string_of_lid uu____7233  in
            FStar_Util.JsonStr uu____7231  in
          ("lid", uu____7230)  in
        [uu____7224; ("type", (FStar_Util.JsonStr typ_str))]  in
      FStar_Util.JsonAssoc uu____7216
  
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____7266 -> true
    | uu____7269 -> false
  
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidSearch uu____7279 -> uu____7279
  
let run_search :
  'uuuuuu7288 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'uuuuuu7288)
          FStar_Util.either)
  =
  fun st  ->
    fun search_str  ->
      let tcenv = st.FStar_Interactive_JsonHelper.repl_env  in
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set ()  in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              let uu____7334 = FStar_Ident.string_of_lid candidate.sc_lid  in
              FStar_Util.contains uu____7334 str
          | TypeContainsLid lid ->
              let uu____7337 = sc_fvars tcenv candidate  in
              FStar_Util.set_mem lid uu____7337
           in
        found <> term.st_negate  in
      let parse search_str1 =
        let parse_one term =
          let negate = FStar_Util.starts_with term "-"  in
          let term1 =
            if negate
            then FStar_Util.substring_from term Prims.int_one
            else term  in
          let beg_quote = FStar_Util.starts_with term1 "\""  in
          let end_quote = FStar_Util.ends_with term1 "\""  in
          let strip_quotes str =
            if (FStar_String.length str) < (Prims.of_int (2))
            then FStar_Exn.raise (InvalidSearch "Empty search term")
            else
              FStar_Util.substring str Prims.int_one
                ((FStar_String.length term1) - (Prims.of_int (2)))
             in
          let parsed =
            if beg_quote <> end_quote
            then
              let uu____7396 =
                let uu____7397 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1
                   in
                InvalidSearch uu____7397  in
              FStar_Exn.raise uu____7396
            else
              if beg_quote
              then
                (let uu____7403 = strip_quotes term1  in
                 NameContainsStr uu____7403)
              else
                (let lid = FStar_Ident.lid_of_str term1  in
                 let uu____7408 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid
                    in
                 match uu____7408 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7411 =
                       let uu____7412 =
                         FStar_Util.format1 "Unknown identifier: %s" term1
                          in
                       InvalidSearch uu____7412  in
                     FStar_Exn.raise uu____7411
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1)
             in
          { st_negate = negate; st_term = parsed }  in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ")  in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term)  in
        FStar_Util.sort_with cmp terms  in
      let pprint_one term =
        let uu____7440 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l ->
              let uu____7447 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "%s" uu____7447
           in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____7440  in
      let results =
        try
          (fun uu___925_7476  ->
             match () with
             | () ->
                 let terms = parse search_str  in
                 let all_lidents = FStar_TypeChecker_Env.lidents tcenv  in
                 let all_candidates = FStar_List.map sc_of_lid all_lidents
                    in
                 let matches_all candidate =
                   FStar_List.for_all (st_matches candidate) terms  in
                 let cmp r1 r2 =
                   let uu____7509 = FStar_Ident.string_of_lid r1.sc_lid  in
                   let uu____7511 = FStar_Ident.string_of_lid r2.sc_lid  in
                   FStar_Util.compare uu____7509 uu____7511  in
                 let results = FStar_List.filter matches_all all_candidates
                    in
                 let sorted = FStar_Util.sort_with cmp results  in
                 let js = FStar_List.map (json_of_search_result tcenv) sorted
                    in
                 (match results with
                  | [] ->
                      let kwds =
                        let uu____7528 = FStar_List.map pprint_one terms  in
                        FStar_Util.concat_l " " uu____7528  in
                      let uu____7534 =
                        let uu____7535 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds
                           in
                        InvalidSearch uu____7535  in
                      FStar_Exn.raise uu____7534
                  | uu____7542 -> (QueryOK, (FStar_Util.JsonList js)))) ()
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s))  in
      (results, (FStar_Util.Inl st))
  
let (run_query :
  FStar_Interactive_JsonHelper.repl_state ->
    query' ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun q  ->
      match q with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | GenericError message -> run_generic_error st message
      | ProtocolViolation query1 -> run_protocol_violation st query1
      | Segment c -> run_segment st c
      | VfsAdd (fname,contents) -> run_vfs_add st fname contents
      | Push pquery -> run_push st pquery
      | Pop  -> run_pop st
      | AutoComplete (search_term1,context) ->
          run_autocomplete st search_term1 context
      | Lookup (symbol,context,pos_opt,rq_info) ->
          run_lookup st symbol context pos_opt rq_info
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
  
let (validate_query :
  FStar_Interactive_JsonHelper.repl_state -> query -> query) =
  fun st  ->
    fun q  ->
      match q.qq with
      | Push
          { push_kind = FStar_Interactive_PushHelper.SyntaxCheck ;
            push_code = uu____7673; push_line = uu____7674;
            push_column = uu____7675; push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____7681 ->
          (match st.FStar_Interactive_JsonHelper.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____7683 -> q)
  
let (validate_and_run_query :
  FStar_Interactive_JsonHelper.repl_state ->
    query ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun query1  ->
      let query2 = validate_query st query1  in
      FStar_ST.op_Colon_Equals repl_current_qid
        (FStar_Pervasives_Native.Some (query2.qid));
      run_query st query2.qq
  
let (js_repl_eval :
  FStar_Interactive_JsonHelper.repl_state ->
    query ->
      (FStar_Util.json * (FStar_Interactive_JsonHelper.repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun query1  ->
      let uu____7756 = validate_and_run_query st query1  in
      match uu____7756 with
      | ((status,response),st_opt) ->
          let js_response = json_of_response query1.qid status response  in
          (js_response, st_opt)
  
let (js_repl_eval_js :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Util.json ->
      (FStar_Util.json * (FStar_Interactive_JsonHelper.repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun query_js  ->
      let uu____7822 = deserialize_interactive_query query_js  in
      js_repl_eval st uu____7822
  
let (js_repl_eval_str :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string * (FStar_Interactive_JsonHelper.repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun query_str  ->
      let uu____7846 =
        let uu____7856 = parse_interactive_query query_str  in
        js_repl_eval st uu____7856  in
      match uu____7846 with
      | (js_response,st_opt) ->
          let uu____7879 = FStar_Util.string_of_json js_response  in
          (uu____7879, st_opt)
  
let (js_repl_init_opts : unit -> unit) =
  fun uu____7892  ->
    let uu____7893 = FStar_Options.parse_cmd_line ()  in
    match uu____7893 with
    | (res,fnames) ->
        (match res with
         | FStar_Getopt.Error msg ->
             failwith (Prims.op_Hat "repl_init: " msg)
         | FStar_Getopt.Help  -> failwith "repl_init: --help unexpected"
         | FStar_Getopt.Success  ->
             (match fnames with
              | [] ->
                  failwith
                    "repl_init: No file name given in --ide invocation"
              | h::uu____7916::uu____7917 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____7926 -> ()))
  
let rec (go : FStar_Interactive_JsonHelper.repl_state -> Prims.int) =
  fun st  ->
    let query1 =
      read_interactive_query st.FStar_Interactive_JsonHelper.repl_stdin  in
    let uu____7939 = validate_and_run_query st query1  in
    match uu____7939 with
    | ((status,response),state_opt) ->
        (write_response query1.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
  
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref []  in
  let add_one e =
    let uu____7992 =
      let uu____7995 = FStar_ST.op_Bang issues  in e :: uu____7995  in
    FStar_ST.op_Colon_Equals issues uu____7992  in
  let count_errors uu____8049 =
    let issues1 =
      let uu____8053 = FStar_ST.op_Bang issues  in
      FStar_Util.remove_dups (fun i0  -> fun i1  -> i0 = i1) uu____8053  in
    let uu____8083 =
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError) issues1
       in
    FStar_List.length uu____8083  in
  let report uu____8095 =
    let uu____8096 =
      let uu____8099 = FStar_ST.op_Bang issues  in
      FStar_Util.remove_dups (fun i0  -> fun i1  -> i0 = i1) uu____8099  in
    FStar_List.sortWith FStar_Errors.compare_issues uu____8096  in
  let clear uu____8134 = FStar_ST.op_Colon_Equals issues []  in
  {
    FStar_Errors.eh_add_one = add_one;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report;
    FStar_Errors.eh_clear = clear
  } 
let (interactive_printer : (FStar_Util.json -> unit) -> FStar_Util.printer) =
  fun printer  ->
    {
      FStar_Util.printer_prinfo =
        (fun s  -> forward_message printer "info" (FStar_Util.JsonStr s));
      FStar_Util.printer_prwarning =
        (fun s  -> forward_message printer "warning" (FStar_Util.JsonStr s));
      FStar_Util.printer_prerror =
        (fun s  -> forward_message printer "error" (FStar_Util.JsonStr s));
      FStar_Util.printer_prgeneric =
        (fun label  ->
           fun get_string  ->
             fun get_json  ->
               let uu____8195 = get_json ()  in
               forward_message printer label uu____8195)
    }
  
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer  ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
  
let (initial_range : FStar_Range.range) =
  let uu____8209 = FStar_Range.mk_pos Prims.int_one Prims.int_zero  in
  let uu____8212 = FStar_Range.mk_pos Prims.int_one Prims.int_zero  in
  FStar_Range.mk_range "<input>" uu____8209 uu____8212 
let (build_initial_repl_state :
  Prims.string -> FStar_Interactive_JsonHelper.repl_state) =
  fun filename  ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps  in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range  in
    let uu____8226 = FStar_Util.open_stdin ()  in
    {
      FStar_Interactive_JsonHelper.repl_line = Prims.int_one;
      FStar_Interactive_JsonHelper.repl_column = Prims.int_zero;
      FStar_Interactive_JsonHelper.repl_fname = filename;
      FStar_Interactive_JsonHelper.repl_deps_stack = [];
      FStar_Interactive_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_Interactive_JsonHelper.repl_env = env1;
      FStar_Interactive_JsonHelper.repl_stdin = uu____8226;
      FStar_Interactive_JsonHelper.repl_names =
        FStar_Interactive_CompletionTable.empty
    }
  
let interactive_mode' :
  'uuuuuu8242 . FStar_Interactive_JsonHelper.repl_state -> 'uuuuuu8242 =
  fun init_st  ->
    write_hello ();
    (let exit_code =
       let uu____8251 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ())  in
       if uu____8251
       then
         let uu____8255 =
           let uu____8257 = FStar_Options.file_list ()  in
           FStar_List.hd uu____8257  in
         FStar_SMTEncoding_Solver.with_hints_db uu____8255
           (fun uu____8264  -> go init_st)
       else go init_st  in
     FStar_All.exit exit_code)
  
let (interactive_mode : Prims.string -> unit) =
  fun filename  ->
    install_ide_mode_hooks FStar_Interactive_JsonHelper.write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____8278 =
       let uu____8280 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____8280  in
     if uu____8278
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init = build_initial_repl_state filename  in
     let uu____8289 = FStar_Options.trace_error ()  in
     if uu____8289
     then interactive_mode' init
     else
       (try
          (fun uu___1078_8295  ->
             match () with | () -> interactive_mode' init) ()
        with
        | uu___1077_8298 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___1077_8298)))
  