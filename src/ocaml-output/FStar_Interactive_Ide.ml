open Prims
let with_captured_errors' :
  'Auu____28 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____28 FStar_Pervasives_Native.option)
          -> 'Auu____28 FStar_Pervasives_Native.option
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
  'Auu____155 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____155 FStar_Pervasives_Native.option)
          -> 'Auu____155 FStar_Pervasives_Native.option
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
                         (fun _542  -> FStar_Pervasives_Native.Some _542)
                         uu____523)
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
        let debug1 verb task =
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
              ((let uu____720 =
                  let uu____722 =
                    let uu____723 =
                      let uu____728 =
                        let uu____737 =
                          FStar_ST.op_Bang
                            FStar_Interactive_PushHelper.repl_stack
                           in
                        FStar_List.hd uu____737  in
                      FStar_Pervasives_Native.snd uu____728  in
                    FStar_Pervasives_Native.fst uu____723  in
                  task = uu____722  in
                ());
               debug1 "Reverting" task;
               (let st' =
                  FStar_Interactive_PushHelper.pop_repl
                    "run_repl_ls_transactions" st1
                   in
                let dep_graph1 =
                  FStar_TypeChecker_Env.dep_graph
                    st1.FStar_Interactive_JsonHelper.repl_env
                   in
                let st'1 =
                  let uu___121_785 = st'  in
                  let uu____786 =
                    FStar_TypeChecker_Env.set_dep_graph
                      st'.FStar_Interactive_JsonHelper.repl_env dep_graph1
                     in
                  {
                    FStar_Interactive_JsonHelper.repl_line =
                      (uu___121_785.FStar_Interactive_JsonHelper.repl_line);
                    FStar_Interactive_JsonHelper.repl_column =
                      (uu___121_785.FStar_Interactive_JsonHelper.repl_column);
                    FStar_Interactive_JsonHelper.repl_fname =
                      (uu___121_785.FStar_Interactive_JsonHelper.repl_fname);
                    FStar_Interactive_JsonHelper.repl_deps_stack =
                      (uu___121_785.FStar_Interactive_JsonHelper.repl_deps_stack);
                    FStar_Interactive_JsonHelper.repl_curmod =
                      (uu___121_785.FStar_Interactive_JsonHelper.repl_curmod);
                    FStar_Interactive_JsonHelper.repl_env = uu____786;
                    FStar_Interactive_JsonHelper.repl_stdin =
                      (uu___121_785.FStar_Interactive_JsonHelper.repl_stdin);
                    FStar_Interactive_JsonHelper.repl_names =
                      (uu___121_785.FStar_Interactive_JsonHelper.repl_names)
                  }  in
                revert_many st'1 entries))
           in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([],[]) -> FStar_Util.Inl st1
          | (task::tasks2,[]) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____839 = FStar_Options.restore_cmd_line_options false
                   in
                FStar_All.pipe_right uu____839 (fun a1  -> ()));
               (let timestamped_task =
                  FStar_Interactive_PushHelper.update_task_timestamps task
                   in
                let push_kind =
                  let uu____843 = FStar_Options.lax ()  in
                  if uu____843
                  then FStar_Interactive_PushHelper.LaxCheck
                  else FStar_Interactive_PushHelper.FullCheck  in
                let uu____848 =
                  run_repl_transaction st1 push_kind false timestamped_task
                   in
                match uu____848 with
                | (success,st2) ->
                    if success
                    then
                      let uu____868 =
                        let uu___146_869 = st2  in
                        let uu____870 =
                          FStar_ST.op_Bang
                            FStar_Interactive_PushHelper.repl_stack
                           in
                        {
                          FStar_Interactive_JsonHelper.repl_line =
                            (uu___146_869.FStar_Interactive_JsonHelper.repl_line);
                          FStar_Interactive_JsonHelper.repl_column =
                            (uu___146_869.FStar_Interactive_JsonHelper.repl_column);
                          FStar_Interactive_JsonHelper.repl_fname =
                            (uu___146_869.FStar_Interactive_JsonHelper.repl_fname);
                          FStar_Interactive_JsonHelper.repl_deps_stack =
                            uu____870;
                          FStar_Interactive_JsonHelper.repl_curmod =
                            (uu___146_869.FStar_Interactive_JsonHelper.repl_curmod);
                          FStar_Interactive_JsonHelper.repl_env =
                            (uu___146_869.FStar_Interactive_JsonHelper.repl_env);
                          FStar_Interactive_JsonHelper.repl_stdin =
                            (uu___146_869.FStar_Interactive_JsonHelper.repl_stdin);
                          FStar_Interactive_JsonHelper.repl_names =
                            (uu___146_869.FStar_Interactive_JsonHelper.repl_names)
                        }  in
                      aux uu____868 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2,prev::previous1) when
              let uu____914 =
                FStar_Interactive_PushHelper.update_task_timestamps task  in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____914
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2,previous1) ->
              let uu____931 = revert_many st1 previous1  in
              aux uu____931 tasks2 []
           in
        aux st tasks
          (FStar_List.rev st.FStar_Interactive_JsonHelper.repl_deps_stack)
  
let (js_pushkind : FStar_Util.json -> FStar_Interactive_PushHelper.push_kind)
  =
  fun s  ->
    let uu____946 = FStar_Interactive_JsonHelper.js_str s  in
    match uu____946 with
    | "syntax" -> FStar_Interactive_PushHelper.SyntaxCheck
    | "lax" -> FStar_Interactive_PushHelper.LaxCheck
    | "full" -> FStar_Interactive_PushHelper.FullCheck
    | uu____951 -> FStar_Interactive_JsonHelper.js_fail "push_kind" s
  
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s  ->
    let uu____960 = FStar_Interactive_JsonHelper.js_str s  in
    match uu____960 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____968 -> FStar_Interactive_JsonHelper.js_fail "reduction rule" s
  
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____997 -> false
  
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____1010 -> false
  
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee  -> match projectee with | CKOption _0 -> _0 
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____1038 -> false
  
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0 
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1076 = FStar_Interactive_JsonHelper.js_str k1  in
        (match uu____1076 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____1104 ->
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
    match projectee with | LKSymbolOnly  -> true | uu____1116 -> false
  
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____1127 -> false
  
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____1138 -> false
  
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____1149 -> false
  
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1162 = FStar_Interactive_JsonHelper.js_str k1  in
        (match uu____1162 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____1172 ->
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
    match projectee with | Exit  -> true | uu____1289 -> false
  
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1300 -> false
  
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1311 -> false
  
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____1324 -> false
  
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Segment _0 -> _0 
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1345 -> false 
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1357 -> false
  
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____1384 -> false
  
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee  -> match projectee with | VfsAdd _0 -> _0 
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1432 -> false
  
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0 
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____1480 -> false
  
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee  -> match projectee with | Lookup _0 -> _0 
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____1550 -> false
  
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Compute _0 -> _0 
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____1597 -> false
  
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Search _0 -> _0 
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____1620 -> false
  
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | GenericError _0 -> _0 
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____1643 -> false
  
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0 
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee  -> match projectee with | { qq; qid;_} -> qq 
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee  -> match projectee with | { qq; qid;_} -> qid 
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___2_1681  ->
    match uu___2_1681 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____1686 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____1690; push_code = uu____1691;
          push_line = uu____1692; push_column = uu____1693;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____1699 -> false
    | GenericError uu____1709 -> false
    | ProtocolViolation uu____1712 -> false
    | Push uu____1715 -> true
    | AutoComplete uu____1717 -> true
    | Lookup uu____1724 -> true
    | Compute uu____1740 -> true
    | Search uu____1751 -> true
  
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
    match projectee with | QueryOK  -> true | uu____1813 -> false
  
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____1824 -> false
  
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____1835 -> false
  
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____1857 =
          let uu____1858 =
            let uu____1860 = FStar_Interactive_JsonHelper.json_debug got  in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1860
             in
          ProtocolViolation uu____1858  in
        { qq = uu____1857; qid }
  
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json  ->
    let assoc1 errloc key a =
      let uu____1889 = FStar_Interactive_JsonHelper.try_assoc key a  in
      match uu____1889 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____1893 =
            let uu____1894 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc  in
            FStar_Interactive_JsonHelper.InvalidQuery uu____1894  in
          FStar_Exn.raise uu____1893
       in
    let request =
      FStar_All.pipe_right json FStar_Interactive_JsonHelper.js_assoc  in
    let qid =
      let uu____1900 = assoc1 "query" "query-id" request  in
      FStar_All.pipe_right uu____1900 FStar_Interactive_JsonHelper.js_str  in
    try
      (fun uu___259_1910  ->
         match () with
         | () ->
             let query =
               let uu____1913 = assoc1 "query" "query" request  in
               FStar_All.pipe_right uu____1913
                 FStar_Interactive_JsonHelper.js_str
                in
             let args =
               let uu____1918 = assoc1 "query" "args" request  in
               FStar_All.pipe_right uu____1918
                 FStar_Interactive_JsonHelper.js_assoc
                in
             let arg1 k = assoc1 "[args]" k args  in
             let try_arg k =
               let uu____1940 = FStar_Interactive_JsonHelper.try_assoc k args
                  in
               match uu____1940 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
                   FStar_Pervasives_Native.None
               | other -> other  in
             let uu____1948 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____1954 =
                     let uu____1956 = arg1 "code"  in
                     FStar_All.pipe_right uu____1956
                       FStar_Interactive_JsonHelper.js_str
                      in
                   Segment uu____1954
               | "peek" ->
                   let uu____1960 =
                     let uu____1961 =
                       let uu____1962 = arg1 "kind"  in
                       FStar_All.pipe_right uu____1962 js_pushkind  in
                     let uu____1964 =
                       let uu____1966 = arg1 "code"  in
                       FStar_All.pipe_right uu____1966
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____1969 =
                       let uu____1971 = arg1 "line"  in
                       FStar_All.pipe_right uu____1971
                         FStar_Interactive_JsonHelper.js_int
                        in
                     let uu____1974 =
                       let uu____1976 = arg1 "column"  in
                       FStar_All.pipe_right uu____1976
                         FStar_Interactive_JsonHelper.js_int
                        in
                     {
                       push_kind = uu____1961;
                       push_code = uu____1964;
                       push_line = uu____1969;
                       push_column = uu____1974;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____1960
               | "push" ->
                   let uu____1982 =
                     let uu____1983 =
                       let uu____1984 = arg1 "kind"  in
                       FStar_All.pipe_right uu____1984 js_pushkind  in
                     let uu____1986 =
                       let uu____1988 = arg1 "code"  in
                       FStar_All.pipe_right uu____1988
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____1991 =
                       let uu____1993 = arg1 "line"  in
                       FStar_All.pipe_right uu____1993
                         FStar_Interactive_JsonHelper.js_int
                        in
                     let uu____1996 =
                       let uu____1998 = arg1 "column"  in
                       FStar_All.pipe_right uu____1998
                         FStar_Interactive_JsonHelper.js_int
                        in
                     {
                       push_kind = uu____1983;
                       push_code = uu____1986;
                       push_line = uu____1991;
                       push_column = uu____1996;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____1982
               | "autocomplete" ->
                   let uu____2004 =
                     let uu____2010 =
                       let uu____2012 = arg1 "partial-symbol"  in
                       FStar_All.pipe_right uu____2012
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____2015 =
                       let uu____2016 = try_arg "context"  in
                       FStar_All.pipe_right uu____2016
                         js_optional_completion_context
                        in
                     (uu____2010, uu____2015)  in
                   AutoComplete uu____2004
               | "lookup" ->
                   let uu____2024 =
                     let uu____2039 =
                       let uu____2041 = arg1 "symbol"  in
                       FStar_All.pipe_right uu____2041
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____2044 =
                       let uu____2045 = try_arg "context"  in
                       FStar_All.pipe_right uu____2045
                         js_optional_lookup_context
                        in
                     let uu____2051 =
                       let uu____2054 =
                         let uu____2057 = try_arg "location"  in
                         FStar_All.pipe_right uu____2057
                           (FStar_Util.map_option
                              FStar_Interactive_JsonHelper.js_assoc)
                          in
                       FStar_All.pipe_right uu____2054
                         (FStar_Util.map_option
                            (fun loc  ->
                               let uu____2083 =
                                 let uu____2085 =
                                   assoc1 "[location]" "filename" loc  in
                                 FStar_All.pipe_right uu____2085
                                   FStar_Interactive_JsonHelper.js_str
                                  in
                               let uu____2089 =
                                 let uu____2091 =
                                   assoc1 "[location]" "line" loc  in
                                 FStar_All.pipe_right uu____2091
                                   FStar_Interactive_JsonHelper.js_int
                                  in
                               let uu____2095 =
                                 let uu____2097 =
                                   assoc1 "[location]" "column" loc  in
                                 FStar_All.pipe_right uu____2097
                                   FStar_Interactive_JsonHelper.js_int
                                  in
                               (uu____2083, uu____2089, uu____2095)))
                        in
                     let uu____2104 =
                       let uu____2108 = arg1 "requested-info"  in
                       FStar_All.pipe_right uu____2108
                         (FStar_Interactive_JsonHelper.js_list
                            FStar_Interactive_JsonHelper.js_str)
                        in
                     (uu____2039, uu____2044, uu____2051, uu____2104)  in
                   Lookup uu____2024
               | "compute" ->
                   let uu____2121 =
                     let uu____2131 =
                       let uu____2133 = arg1 "term"  in
                       FStar_All.pipe_right uu____2133
                         FStar_Interactive_JsonHelper.js_str
                        in
                     let uu____2136 =
                       let uu____2141 = try_arg "rules"  in
                       FStar_All.pipe_right uu____2141
                         (FStar_Util.map_option
                            (FStar_Interactive_JsonHelper.js_list
                               js_reductionrule))
                        in
                     (uu____2131, uu____2136)  in
                   Compute uu____2121
               | "search" ->
                   let uu____2159 =
                     let uu____2161 = arg1 "terms"  in
                     FStar_All.pipe_right uu____2161
                       FStar_Interactive_JsonHelper.js_str
                      in
                   Search uu____2159
               | "vfs-add" ->
                   let uu____2165 =
                     let uu____2174 =
                       let uu____2178 = try_arg "filename"  in
                       FStar_All.pipe_right uu____2178
                         (FStar_Util.map_option
                            FStar_Interactive_JsonHelper.js_str)
                        in
                     let uu____2188 =
                       let uu____2190 = arg1 "contents"  in
                       FStar_All.pipe_right uu____2190
                         FStar_Interactive_JsonHelper.js_str
                        in
                     (uu____2174, uu____2188)  in
                   VfsAdd uu____2165
               | uu____2197 ->
                   let uu____2199 =
                     FStar_Util.format1 "Unknown query '%s'" query  in
                   ProtocolViolation uu____2199
                in
             { qq = uu____1948; qid }) ()
    with
    | FStar_Interactive_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected,got) ->
        wrap_js_failure qid expected got
  
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query  ->
    try
      (fun uu___294_2218  ->
         match () with | () -> unpack_interactive_query js_query) ()
    with
    | FStar_Interactive_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid = "?" }
    | FStar_Interactive_JsonHelper.UnexpectedJsonType (expected,got) ->
        wrap_js_failure "?" expected got
  
let (parse_interactive_query : Prims.string -> query) =
  fun query_str  ->
    let uu____2238 = FStar_Util.json_of_string query_str  in
    match uu____2238 with
    | FStar_Pervasives_Native.None  ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
  
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream  ->
    let uu____2250 = FStar_Util.read_line stream  in
    match uu____2250 with
    | FStar_Pervasives_Native.None  -> FStar_All.exit Prims.int_zero
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
  
let json_of_opt :
  'Auu____2266 .
    ('Auu____2266 -> FStar_Util.json) ->
      'Auu____2266 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2286 = FStar_Util.map_option json_of_a opt_a  in
      FStar_Util.dflt FStar_Util.JsonNull uu____2286
  
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
    let uu____2306 =
      let uu____2314 =
        let uu____2322 =
          let uu____2330 =
            let uu____2336 =
              let uu____2337 =
                let uu____2340 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2346 = FStar_Range.json_of_use_range r  in
                      [uu____2346]
                   in
                let uu____2347 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____2353 = FStar_Range.def_range r  in
                      let uu____2354 = FStar_Range.use_range r  in
                      uu____2353 <> uu____2354 ->
                      let uu____2355 = FStar_Range.json_of_def_range r  in
                      [uu____2355]
                  | uu____2356 -> []  in
                FStar_List.append uu____2340 uu____2347  in
              FStar_Util.JsonList uu____2337  in
            ("ranges", uu____2336)  in
          [uu____2330]  in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2322
         in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2314
       in
    FStar_Util.JsonAssoc uu____2306
  
let (alist_of_symbol_lookup_result :
  FStar_Interactive_QueryHelper.sl_reponse ->
    (Prims.string * FStar_Util.json) Prims.list)
  =
  fun lr  ->
    let uu____2398 =
      let uu____2406 =
        let uu____2412 =
          json_of_opt FStar_Range.json_of_def_range
            lr.FStar_Interactive_QueryHelper.slr_def_range
           in
        ("defined-at", uu____2412)  in
      let uu____2415 =
        let uu____2423 =
          let uu____2429 =
            json_of_opt (fun _2431  -> FStar_Util.JsonStr _2431)
              lr.FStar_Interactive_QueryHelper.slr_typ
             in
          ("type", uu____2429)  in
        let uu____2434 =
          let uu____2442 =
            let uu____2448 =
              json_of_opt (fun _2450  -> FStar_Util.JsonStr _2450)
                lr.FStar_Interactive_QueryHelper.slr_doc
               in
            ("documentation", uu____2448)  in
          let uu____2453 =
            let uu____2461 =
              let uu____2467 =
                json_of_opt (fun _2469  -> FStar_Util.JsonStr _2469)
                  lr.FStar_Interactive_QueryHelper.slr_def
                 in
              ("definition", uu____2467)  in
            [uu____2461]  in
          uu____2442 :: uu____2453  in
        uu____2423 :: uu____2434  in
      uu____2406 :: uu____2415  in
    ("name",
      (FStar_Util.JsonStr (lr.FStar_Interactive_QueryHelper.slr_name))) ::
      uu____2398
  
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____2514 =
      FStar_List.map (fun _2518  -> FStar_Util.JsonStr _2518)
        interactive_protocol_features
       in
    FStar_All.pipe_left (fun _2521  -> FStar_Util.JsonList _2521) uu____2514
     in
  [("version", js_version); ("features", js_features)] 
type fstar_option_permission_level =
  | OptSet 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____2550 -> false
  
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____2561 -> false
  
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___3_2569  ->
    match uu___3_2569 with | OptSet  -> "" | OptReadOnly  -> "read-only"
  
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
  fun uu___4_2819  ->
    match uu___4_2819 with
    | FStar_Options.Const uu____2821 -> "flag"
    | FStar_Options.IntStr uu____2823 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____2827 -> "path"
    | FStar_Options.SimpleStr uu____2830 -> "string"
    | FStar_Options.EnumStr uu____2833 -> "enum"
    | FStar_Options.OpenEnumStr uu____2838 -> "open enum"
    | FStar_Options.PostProcessed (uu____2848,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____2858,typ) ->
        kind_of_fstar_option_type typ
  
let rec (snippets_of_fstar_option :
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
        | FStar_Options.Const uu____2930 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____2968,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____2978,elem_spec) ->
            arg_snippets_of_type elem_spec
         in
      let uu____2986 = arg_snippets_of_type typ  in
      FStar_List.map (mk_snippet name) uu____2986
  
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___5_2997  ->
    match uu___5_2997 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____3009 = FStar_List.map json_of_fstar_option_value vs  in
        FStar_Util.JsonList uu____3009
    | FStar_Options.Unset  -> FStar_Util.JsonNull
  
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt  ->
    let uu____3025 =
      let uu____3033 =
        let uu____3041 =
          let uu____3047 = json_of_fstar_option_value opt.opt_value  in
          ("value", uu____3047)  in
        let uu____3050 =
          let uu____3058 =
            let uu____3064 = json_of_fstar_option_value opt.opt_default  in
            ("default", uu____3064)  in
          let uu____3067 =
            let uu____3075 =
              let uu____3081 =
                json_of_opt (fun _3083  -> FStar_Util.JsonStr _3083)
                  opt.opt_documentation
                 in
              ("documentation", uu____3081)  in
            let uu____3086 =
              let uu____3094 =
                let uu____3100 =
                  let uu____3101 = kind_of_fstar_option_type opt.opt_type  in
                  FStar_Util.JsonStr uu____3101  in
                ("type", uu____3100)  in
              [uu____3094;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))]
               in
            uu____3075 :: uu____3086  in
          uu____3058 :: uu____3067  in
        uu____3041 :: uu____3050  in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____3033  in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3025
  
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt  ->
    let uu____3157 = alist_of_fstar_option opt  in
    FStar_Util.JsonAssoc uu____3157
  
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
      let uu____3253 =
        let uu____3261 =
          let uu____3269 =
            let uu____3275 =
              let uu____3276 = FStar_ST.op_Bang repl_current_qid  in
              json_of_opt (fun _3306  -> FStar_Util.JsonStr _3306) uu____3276
               in
            ("query-id", uu____3275)  in
          [uu____3269;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)]  in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____3261  in
      FStar_Util.JsonAssoc uu____3253
  
let forward_message :
  'Auu____3350 .
    (FStar_Util.json -> 'Auu____3350) ->
      Prims.string -> FStar_Util.json -> 'Auu____3350
  =
  fun callback  ->
    fun level  ->
      fun contents  ->
        let uu____3373 = json_of_message level contents  in
        callback uu____3373
  
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____3377 =
      FStar_List.map (fun _3381  -> FStar_Util.JsonStr _3381)
        interactive_protocol_features
       in
    FStar_Util.JsonList uu____3377  in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
  
let (write_hello : unit -> unit) =
  fun uu____3395  -> FStar_Interactive_JsonHelper.write_json json_of_hello 
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name  ->
    fun typ  ->
      let flag = Prims.op_Hat "--" name  in
      let uu____3413 = FStar_Options.desc_of_opt_type typ  in
      match uu____3413 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
  
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults  in
  let uu____3429 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____3464  ->
            match uu____3464 with
            | (_shortname,name,typ,doc1) ->
                let uu____3488 = FStar_Util.smap_try_find defaults1 name  in
                FStar_All.pipe_right uu____3488
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____3500 = sig_of_fstar_option name typ  in
                        let uu____3502 = snippets_of_fstar_option name typ
                           in
                        let uu____3506 =
                          let uu____3507 = FStar_Options.settable name  in
                          if uu____3507 then OptSet else OptReadOnly  in
                        {
                          opt_name = name;
                          opt_sig = uu____3500;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____3502;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____3506
                        }))))
     in
  FStar_All.pipe_right uu____3429
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
    let uu___464_3546 = opt  in
    let uu____3547 = FStar_Options.get_option opt.opt_name  in
    {
      opt_name = (uu___464_3546.opt_name);
      opt_sig = (uu___464_3546.opt_sig);
      opt_value = uu____3547;
      opt_default = (uu___464_3546.opt_default);
      opt_type = (uu___464_3546.opt_type);
      opt_snippets = (uu___464_3546.opt_snippets);
      opt_documentation = (uu___464_3546.opt_documentation);
      opt_permission_level = (uu___464_3546.opt_permission_level)
    }
  
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1  ->
    let uu____3563 = FStar_List.filter filter1 fstar_options_list_cache  in
    FStar_List.map update_option uu____3563
  
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name  ->
    let opt_prefix = "--"  in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____3590 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix)
         in
      (opt_prefix, uu____3590)
    else ("", opt_name)
  
let (json_of_repl_state :
  FStar_Interactive_JsonHelper.repl_state -> FStar_Util.json) =
  fun st  ->
    let filenames uu____3621 =
      match uu____3621 with
      | (uu____3633,(task,uu____3635)) ->
          (match task with
           | FStar_Interactive_JsonHelper.LDInterleaved (intf,impl) ->
               [intf.FStar_Interactive_JsonHelper.tf_fname;
               impl.FStar_Interactive_JsonHelper.tf_fname]
           | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
               [intf_or_impl.FStar_Interactive_JsonHelper.tf_fname]
           | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
               [intf.FStar_Interactive_JsonHelper.tf_fname]
           | uu____3654 -> [])
       in
    let uu____3656 =
      let uu____3664 =
        let uu____3670 =
          let uu____3671 =
            let uu____3674 =
              FStar_List.concatMap filenames
                st.FStar_Interactive_JsonHelper.repl_deps_stack
               in
            FStar_List.map (fun _3688  -> FStar_Util.JsonStr _3688)
              uu____3674
             in
          FStar_Util.JsonList uu____3671  in
        ("loaded-dependencies", uu____3670)  in
      let uu____3691 =
        let uu____3699 =
          let uu____3705 =
            let uu____3706 =
              let uu____3709 =
                current_fstar_options (fun uu____3714  -> true)  in
              FStar_List.map json_of_fstar_option uu____3709  in
            FStar_Util.JsonList uu____3706  in
          ("options", uu____3705)  in
        [uu____3699]  in
      uu____3664 :: uu____3691  in
    FStar_Util.JsonAssoc uu____3656
  
let run_exit :
  'Auu____3740 'Auu____3741 .
    'Auu____3740 ->
      ((query_status * FStar_Util.json) * ('Auu____3741,Prims.int)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr Prims.int_zero))
  
let run_describe_protocol :
  'Auu____3778 'Auu____3779 .
    'Auu____3778 ->
      ((query_status * FStar_Util.json) * ('Auu____3778,'Auu____3779)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
  
let run_describe_repl :
  'Auu____3810 .
    FStar_Interactive_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state,'Auu____3810)
        FStar_Util.either)
  =
  fun st  ->
    let uu____3828 =
      let uu____3833 = json_of_repl_state st  in (QueryOK, uu____3833)  in
    (uu____3828, (FStar_Util.Inl st))
  
let run_protocol_violation :
  'Auu____3851 'Auu____3852 .
    'Auu____3851 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____3851,'Auu____3852)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
  
let run_generic_error :
  'Auu____3894 'Auu____3895 .
    'Auu____3894 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____3894,'Auu____3895)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
  
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____3935  ->
    let errors = FStar_Errors.report_all ()  in FStar_Errors.clear (); errors
  
let run_segment :
  'Auu____3947 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'Auu____3947)
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
      let collect_decls uu____3983 =
        let uu____3984 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____3984 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____3990,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____3996,decls,uu____3998)) -> decls
         in
      let uu____4005 =
        with_captured_errors st.FStar_Interactive_JsonHelper.repl_env
          FStar_Util.sigint_ignore
          (fun uu____4014  ->
             let uu____4015 = collect_decls ()  in
             FStar_All.pipe_left
               (fun _4026  -> FStar_Pervasives_Native.Some _4026) uu____4015)
         in
      match uu____4005 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____4044 = collect_errors ()  in
            FStar_All.pipe_right uu____4044 (FStar_List.map json_of_issue)
             in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____4070 =
              let uu____4078 =
                let uu____4084 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl)
                   in
                ("def_range", uu____4084)  in
              [uu____4078]  in
            FStar_Util.JsonAssoc uu____4070  in
          let js_decls =
            let uu____4098 = FStar_List.map json_of_decl decls  in
            FStar_All.pipe_left (fun _4103  -> FStar_Util.JsonList _4103)
              uu____4098
             in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
  
let run_vfs_add :
  'Auu____4133 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state,'Auu____4133)
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
  'Auu____4186 .
    FStar_Interactive_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state,'Auu____4186)
        FStar_Util.either)
  =
  fun st  ->
    let uu____4204 = nothing_left_to_pop st  in
    if uu____4204
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
      let uu____4291 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents)  in
      FStar_Interactive_JsonHelper.write_json uu____4291
  
let (write_repl_ld_task_progress :
  FStar_Interactive_JsonHelper.repl_task -> unit) =
  fun task  ->
    match task with
    | FStar_Interactive_JsonHelper.LDInterleaved (uu____4299,tf) ->
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
    | uu____4351 -> ()
  
let (load_deps :
  FStar_Interactive_JsonHelper.repl_state ->
    ((FStar_Interactive_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_Interactive_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st  ->
    let uu____4369 =
      with_captured_errors st.FStar_Interactive_JsonHelper.repl_env
        FStar_Util.sigint_ignore
        (fun _env  ->
           let uu____4397 =
             FStar_Interactive_PushHelper.deps_and_repl_ld_tasks_of_our_file
               st.FStar_Interactive_JsonHelper.repl_fname
              in
           FStar_All.pipe_left
             (fun _4444  -> FStar_Pervasives_Native.Some _4444) uu____4397)
       in
    match uu____4369 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph1) ->
        let st1 =
          let uu___554_4499 = st  in
          let uu____4500 =
            FStar_TypeChecker_Env.set_dep_graph
              st.FStar_Interactive_JsonHelper.repl_env dep_graph1
             in
          {
            FStar_Interactive_JsonHelper.repl_line =
              (uu___554_4499.FStar_Interactive_JsonHelper.repl_line);
            FStar_Interactive_JsonHelper.repl_column =
              (uu___554_4499.FStar_Interactive_JsonHelper.repl_column);
            FStar_Interactive_JsonHelper.repl_fname =
              (uu___554_4499.FStar_Interactive_JsonHelper.repl_fname);
            FStar_Interactive_JsonHelper.repl_deps_stack =
              (uu___554_4499.FStar_Interactive_JsonHelper.repl_deps_stack);
            FStar_Interactive_JsonHelper.repl_curmod =
              (uu___554_4499.FStar_Interactive_JsonHelper.repl_curmod);
            FStar_Interactive_JsonHelper.repl_env = uu____4500;
            FStar_Interactive_JsonHelper.repl_stdin =
              (uu___554_4499.FStar_Interactive_JsonHelper.repl_stdin);
            FStar_Interactive_JsonHelper.repl_names =
              (uu___554_4499.FStar_Interactive_JsonHelper.repl_names)
          }  in
        let uu____4501 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress  in
        (match uu____4501 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
  
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue  ->
    let uu___564_4556 = issue  in
    let uu____4557 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message
       in
    {
      FStar_Errors.issue_message = uu____4557;
      FStar_Errors.issue_level = (uu___564_4556.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___564_4556.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___564_4556.FStar_Errors.issue_number)
    }
  
let run_push_without_deps :
  'Auu____4567 .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'Auu____4567)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let set_nosynth_flag st1 flag =
        let uu___571_4603 = st1  in
        {
          FStar_Interactive_JsonHelper.repl_line =
            (uu___571_4603.FStar_Interactive_JsonHelper.repl_line);
          FStar_Interactive_JsonHelper.repl_column =
            (uu___571_4603.FStar_Interactive_JsonHelper.repl_column);
          FStar_Interactive_JsonHelper.repl_fname =
            (uu___571_4603.FStar_Interactive_JsonHelper.repl_fname);
          FStar_Interactive_JsonHelper.repl_deps_stack =
            (uu___571_4603.FStar_Interactive_JsonHelper.repl_deps_stack);
          FStar_Interactive_JsonHelper.repl_curmod =
            (uu___571_4603.FStar_Interactive_JsonHelper.repl_curmod);
          FStar_Interactive_JsonHelper.repl_env =
            (let uu___573_4605 = st1.FStar_Interactive_JsonHelper.repl_env
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___573_4605.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___573_4605.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___573_4605.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___573_4605.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___573_4605.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___573_4605.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___573_4605.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___573_4605.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___573_4605.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___573_4605.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___573_4605.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___573_4605.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___573_4605.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___573_4605.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___573_4605.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___573_4605.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___573_4605.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___573_4605.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___573_4605.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___573_4605.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___573_4605.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___573_4605.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___573_4605.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___573_4605.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___573_4605.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___573_4605.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___573_4605.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___573_4605.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___573_4605.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___573_4605.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___573_4605.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___573_4605.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___573_4605.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___573_4605.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___573_4605.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___573_4605.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___573_4605.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___573_4605.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___573_4605.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___573_4605.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___573_4605.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___573_4605.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___573_4605.FStar_TypeChecker_Env.erasable_types_tab)
             });
          FStar_Interactive_JsonHelper.repl_stdin =
            (uu___571_4603.FStar_Interactive_JsonHelper.repl_stdin);
          FStar_Interactive_JsonHelper.repl_names =
            (uu___571_4603.FStar_Interactive_JsonHelper.repl_names)
        }  in
      let uu____4606 = query  in
      match uu____4606 with
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
            let uu____4633 =
              run_repl_transaction st1 push_kind peek_only
                (FStar_Interactive_JsonHelper.PushFragment frag)
               in
            match uu____4633 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false  in
                let status =
                  if success || peek_only then QueryOK else QueryNOK  in
                let json_errors =
                  let uu____4662 =
                    let uu____4665 = collect_errors ()  in
                    FStar_All.pipe_right uu____4665
                      (FStar_List.map json_of_issue)
                     in
                  FStar_Util.JsonList uu____4662  in
                let st4 =
                  if success
                  then
                    let uu___592_4674 = st3  in
                    {
                      FStar_Interactive_JsonHelper.repl_line = line;
                      FStar_Interactive_JsonHelper.repl_column = column;
                      FStar_Interactive_JsonHelper.repl_fname =
                        (uu___592_4674.FStar_Interactive_JsonHelper.repl_fname);
                      FStar_Interactive_JsonHelper.repl_deps_stack =
                        (uu___592_4674.FStar_Interactive_JsonHelper.repl_deps_stack);
                      FStar_Interactive_JsonHelper.repl_curmod =
                        (uu___592_4674.FStar_Interactive_JsonHelper.repl_curmod);
                      FStar_Interactive_JsonHelper.repl_env =
                        (uu___592_4674.FStar_Interactive_JsonHelper.repl_env);
                      FStar_Interactive_JsonHelper.repl_stdin =
                        (uu___592_4674.FStar_Interactive_JsonHelper.repl_stdin);
                      FStar_Interactive_JsonHelper.repl_names =
                        (uu___592_4674.FStar_Interactive_JsonHelper.repl_names)
                    }
                  else st3  in
                ((status, json_errors), (FStar_Util.Inl st4))))
  
let run_push_with_deps :
  'Auu____4692 .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'Auu____4692)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      (let uu____4716 = FStar_Options.debug_any ()  in
       if uu____4716
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info
        st.FStar_Interactive_JsonHelper.repl_env false;
      (let uu____4724 = load_deps st  in
       match uu____4724 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____4759 = collect_errors ()  in
             FStar_List.map rephrase_dependency_error uu____4759  in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue)  in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____4793 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____4793 (fun a2  -> ()));
            (let names1 =
               FStar_Interactive_PushHelper.add_module_completions
                 st1.FStar_Interactive_JsonHelper.repl_fname deps
                 st1.FStar_Interactive_JsonHelper.repl_names
                in
             run_push_without_deps
               (let uu___610_4797 = st1  in
                {
                  FStar_Interactive_JsonHelper.repl_line =
                    (uu___610_4797.FStar_Interactive_JsonHelper.repl_line);
                  FStar_Interactive_JsonHelper.repl_column =
                    (uu___610_4797.FStar_Interactive_JsonHelper.repl_column);
                  FStar_Interactive_JsonHelper.repl_fname =
                    (uu___610_4797.FStar_Interactive_JsonHelper.repl_fname);
                  FStar_Interactive_JsonHelper.repl_deps_stack =
                    (uu___610_4797.FStar_Interactive_JsonHelper.repl_deps_stack);
                  FStar_Interactive_JsonHelper.repl_curmod =
                    (uu___610_4797.FStar_Interactive_JsonHelper.repl_curmod);
                  FStar_Interactive_JsonHelper.repl_env =
                    (uu___610_4797.FStar_Interactive_JsonHelper.repl_env);
                  FStar_Interactive_JsonHelper.repl_stdin =
                    (uu___610_4797.FStar_Interactive_JsonHelper.repl_stdin);
                  FStar_Interactive_JsonHelper.repl_names = names1
                }) query)))
  
let run_push :
  'Auu____4805 .
    FStar_Interactive_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'Auu____4805)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let uu____4828 = nothing_left_to_pop st  in
      if uu____4828
      then run_push_with_deps st query
      else run_push_without_deps st query
  
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
          let uu____4895 =
            FStar_Interactive_QueryHelper.symlookup
              st.FStar_Interactive_JsonHelper.repl_env symbol pos_opt
              requested_info
             in
          match uu____4895 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some result ->
              let uu____4930 =
                let uu____4943 = alist_of_symbol_lookup_result result  in
                ("symbol", uu____4943)  in
              FStar_Util.Inr uu____4930
  
let (run_option_lookup :
  Prims.string ->
    (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                    Prims.list))
      FStar_Util.either)
  =
  fun opt_name  ->
    let uu____4998 = trim_option_name opt_name  in
    match uu____4998 with
    | (uu____5022,trimmed_name) ->
        let uu____5028 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name  in
        (match uu____5028 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____5063 =
               let uu____5076 =
                 let uu____5084 = update_option opt  in
                 alist_of_fstar_option uu____5084  in
               ("option", uu____5076)  in
             FStar_Util.Inr uu____5063)
  
let (run_module_lookup :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                      Prims.list))
        FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      let query = FStar_Util.split symbol "."  in
      let uu____5142 =
        FStar_Interactive_CompletionTable.find_module_or_ns
          st.FStar_Interactive_JsonHelper.repl_names query
         in
      match uu____5142 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____5177 =
            let uu____5190 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info
               in
            ("module", uu____5190)  in
          FStar_Util.Inr uu____5177
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____5221 =
            let uu____5234 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info  in
            ("namespace", uu____5234)  in
          FStar_Util.Inr uu____5221
  
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
          let uu____5314 = run_symbol_lookup st symbol pos_opt requested_info
             in
          match uu____5314 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____5388 ->
              let uu____5403 = run_module_lookup st symbol  in
              (match uu____5403 with
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
  'Auu____5591 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        lookup_context ->
          FStar_Interactive_QueryHelper.position
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) *
                (FStar_Interactive_JsonHelper.repl_state,'Auu____5591)
                FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____5641 =
              run_lookup' st symbol context pos_opt requested_info  in
            match uu____5641 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
  
let run_code_autocomplete :
  'Auu____5747 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'Auu____5747)
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
  'Auu____5801 'Auu____5802 'Auu____5803 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        'Auu____5801 ->
          'Auu____5802 ->
            ((query_status * FStar_Util.json) *
              (FStar_Interactive_JsonHelper.repl_state,'Auu____5803)
              FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun modules1  ->
        fun namespaces  ->
          let needle = FStar_Util.split search_term "."  in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.FStar_Interactive_JsonHelper.repl_names needle
              (fun _5850  -> FStar_Pervasives_Native.Some _5850)
             in
          let json =
            FStar_List.map
              FStar_Interactive_CompletionTable.json_of_completion_result
              mods_and_nss
             in
          ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
  
let candidates_of_fstar_option :
  'Auu____5871 .
    Prims.int ->
      'Auu____5871 ->
        fstar_option ->
          FStar_Interactive_CompletionTable.completion_result Prims.list
  =
  fun match_len  ->
    fun is_reset  ->
      fun opt  ->
        let uu____5891 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReadOnly  -> (false, "read-only")  in
        match uu____5891 with
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
  'Auu____5953 'Auu____5954 'Auu____5955 .
    'Auu____5953 ->
      Prims.string ->
        'Auu____5954 ->
          ((query_status * FStar_Util.json) * ('Auu____5953,'Auu____5955)
            FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____5985 = trim_option_name search_term  in
        match uu____5985 with
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
        | (uu____6041,uu____6042) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
  
let run_autocomplete :
  'Auu____6065 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state,'Auu____6065)
            FStar_Util.either)
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
  
let run_and_rewind :
  'Auu____6117 'Auu____6118 .
    FStar_Interactive_JsonHelper.repl_state ->
      'Auu____6117 ->
        (FStar_Interactive_JsonHelper.repl_state -> 'Auu____6117) ->
          ('Auu____6117 *
            (FStar_Interactive_JsonHelper.repl_state,'Auu____6118)
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
            (fun uu___725_6159  ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____6170  ->
                        let uu____6171 = task st1  in
                        FStar_All.pipe_left
                          (fun _6176  -> FStar_Util.Inl _6176) uu____6171))
              ()
          with | FStar_Util.SigInt  -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e  in
        let st2 = FStar_Interactive_PushHelper.pop_repl "run_and_rewind" st1
           in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
  
let run_with_parsed_and_tc_term :
  'Auu____6225 'Auu____6226 'Auu____6227 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        'Auu____6225 ->
          'Auu____6226 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) *
                (FStar_Interactive_JsonHelper.repl_state,'Auu____6227)
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
                    ((uu____6329,{ FStar_Syntax_Syntax.lbname = uu____6330;
                                   FStar_Syntax_Syntax.lbunivs = univs1;
                                   FStar_Syntax_Syntax.lbtyp = uu____6332;
                                   FStar_Syntax_Syntax.lbeff = uu____6333;
                                   FStar_Syntax_Syntax.lbdef = def;
                                   FStar_Syntax_Syntax.lbattrs = uu____6335;
                                   FStar_Syntax_Syntax.lbpos = uu____6336;_}::[]),uu____6337);
                  FStar_Syntax_Syntax.sigrng = uu____6338;
                  FStar_Syntax_Syntax.sigquals = uu____6339;
                  FStar_Syntax_Syntax.sigmeta = uu____6340;
                  FStar_Syntax_Syntax.sigattrs = uu____6341;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____6380 -> FStar_Pervasives_Native.None  in
            let parse1 frag =
              let uu____6401 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag)
                 in
              match uu____6401 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____6407) ->
                  FStar_Pervasives_Native.Some decls
              | uu____6428 -> FStar_Pervasives_Native.None  in
            let desugar env decls =
              let uu____6446 =
                let uu____6451 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls  in
                uu____6451 env.FStar_TypeChecker_Env.dsenv  in
              FStar_Pervasives_Native.fst uu____6446  in
            let typecheck tcenv decls =
              let uu____6473 = FStar_TypeChecker_Tc.tc_decls tcenv decls  in
              match uu____6473 with | (ses,uu____6487,uu____6488) -> ses  in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1  ->
                 let tcenv = st1.FStar_Interactive_JsonHelper.repl_env  in
                 let frag = dummy_let_fragment term  in
                 let uu____6509 = parse1 frag  in
                 match uu____6509 with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____6535 =
                       let decls1 = desugar tcenv decls  in
                       let ses = typecheck tcenv decls1  in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1,def) ->
                           let uu____6571 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def  in
                           (match uu____6571 with
                            | (univs2,def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2
                                   in
                                continuation tcenv1 def1)
                        in
                     let uu____6583 = FStar_Options.trace_error ()  in
                     if uu____6583
                     then aux ()
                     else
                       (try
                          (fun uu___808_6597  -> match () with | () -> aux ())
                            ()
                        with
                        | uu___807_6606 ->
                            let uu____6611 =
                              FStar_Errors.issue_of_exn uu___807_6606  in
                            (match uu____6611 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____6619 =
                                   let uu____6620 =
                                     FStar_Errors.format_issue issue  in
                                   FStar_Util.JsonStr uu____6620  in
                                 (QueryNOK, uu____6619)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Exn.raise uu___807_6606)))
  
let run_compute :
  'Auu____6635 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) *
            (FStar_Interactive_JsonHelper.repl_state,'Auu____6635)
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
        let normalize_term1 tcenv rules2 t =
          FStar_TypeChecker_Normalize.normalize rules2 tcenv t  in
        run_with_parsed_and_tc_term st term Prims.int_zero Prims.int_zero
          (fun tcenv  ->
             fun def  ->
               let normalized = normalize_term1 tcenv rules1 def  in
               let uu____6713 =
                 let uu____6714 =
                   FStar_Interactive_QueryHelper.term_to_string tcenv
                     normalized
                    in
                 FStar_Util.JsonStr uu____6714  in
               (QueryOK, uu____6713))
  
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____6749 -> false
  
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0 
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____6771 -> false
  
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0 
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | { st_negate; st_term;_} -> st_negate
  
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee  -> match projectee with | { st_negate; st_term;_} -> st_term 
let (st_cost : search_term' -> Prims.int) =
  fun uu___6_6806  ->
    match uu___6_6806 with
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
    let uu____6940 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    let uu____6947 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    { sc_lid = lid; sc_typ = uu____6940; sc_fvars = uu____6947 }
  
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv  ->
    fun sc  ->
      let uu____6971 = FStar_ST.op_Bang sc.sc_typ  in
      match uu____6971 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____6999 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid  in
            match uu____6999 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7018,typ),uu____7020) ->
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
      let uu____7070 = FStar_ST.op_Bang sc.sc_fvars  in
      match uu____7070 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____7114 = sc_typ tcenv sc  in
            FStar_Syntax_Free.fvars uu____7114  in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
  
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____7158 = sc_typ tcenv sc  in
        FStar_Interactive_QueryHelper.term_to_string tcenv uu____7158  in
      let uu____7159 =
        let uu____7167 =
          let uu____7173 =
            let uu____7174 =
              let uu____7176 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid
                 in
              uu____7176.FStar_Ident.str  in
            FStar_Util.JsonStr uu____7174  in
          ("lid", uu____7173)  in
        [uu____7167; ("type", (FStar_Util.JsonStr typ_str))]  in
      FStar_Util.JsonAssoc uu____7159
  
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____7209 -> true
    | uu____7212 -> false
  
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidSearch uu____7222 -> uu____7222
  
let run_search :
  'Auu____7231 .
    FStar_Interactive_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) *
          (FStar_Interactive_JsonHelper.repl_state,'Auu____7231)
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
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____7278 = sc_fvars tcenv candidate  in
              FStar_Util.set_mem lid uu____7278
           in
        found <> term.st_negate  in
      let parse1 search_str1 =
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
              let uu____7337 =
                let uu____7338 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1
                   in
                InvalidSearch uu____7338  in
              FStar_Exn.raise uu____7337
            else
              if beg_quote
              then
                (let uu____7344 = strip_quotes term1  in
                 NameContainsStr uu____7344)
              else
                (let lid = FStar_Ident.lid_of_str term1  in
                 let uu____7349 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid
                    in
                 match uu____7349 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7352 =
                       let uu____7353 =
                         FStar_Util.format1 "Unknown identifier: %s" term1
                          in
                       InvalidSearch uu____7353  in
                     FStar_Exn.raise uu____7352
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1)
             in
          { st_negate = negate; st_term = parsed }  in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ")  in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term)  in
        FStar_Util.sort_with cmp terms  in
      let pprint_one term =
        let uu____7381 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str
           in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____7381  in
      let results =
        try
          (fun uu___921_7415  ->
             match () with
             | () ->
                 let terms = parse1 search_str  in
                 let all_lidents = FStar_TypeChecker_Env.lidents tcenv  in
                 let all_candidates = FStar_List.map sc_of_lid all_lidents
                    in
                 let matches_all candidate =
                   FStar_List.for_all (st_matches candidate) terms  in
                 let cmp r1 r2 =
                   FStar_Util.compare (r1.sc_lid).FStar_Ident.str
                     (r2.sc_lid).FStar_Ident.str
                    in
                 let results = FStar_List.filter matches_all all_candidates
                    in
                 let sorted1 = FStar_Util.sort_with cmp results  in
                 let js =
                   FStar_List.map (json_of_search_result tcenv) sorted1  in
                 (match results with
                  | [] ->
                      let kwds =
                        let uu____7463 = FStar_List.map pprint_one terms  in
                        FStar_Util.concat_l " " uu____7463  in
                      let uu____7469 =
                        let uu____7470 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds
                           in
                        InvalidSearch uu____7470  in
                      FStar_Exn.raise uu____7469
                  | uu____7477 -> (QueryOK, (FStar_Util.JsonList js)))) ()
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
  
let (validate_query :
  FStar_Interactive_JsonHelper.repl_state -> query -> query) =
  fun st  ->
    fun q  ->
      match q.qq with
      | Push
          { push_kind = FStar_Interactive_PushHelper.SyntaxCheck ;
            push_code = uu____7608; push_line = uu____7609;
            push_column = uu____7610; push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____7616 ->
          (match st.FStar_Interactive_JsonHelper.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____7618 -> q)
  
let (validate_and_run_query :
  FStar_Interactive_JsonHelper.repl_state ->
    query ->
      ((query_status * FStar_Util.json) *
        (FStar_Interactive_JsonHelper.repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun query  ->
      let query1 = validate_query st query  in
      FStar_ST.op_Colon_Equals repl_current_qid
        (FStar_Pervasives_Native.Some (query1.qid));
      run_query st query1.qq
  
let (js_repl_eval :
  FStar_Interactive_JsonHelper.repl_state ->
    query ->
      (FStar_Util.json * (FStar_Interactive_JsonHelper.repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun query  ->
      let uu____7691 = validate_and_run_query st query  in
      match uu____7691 with
      | ((status,response),st_opt) ->
          let js_response = json_of_response query.qid status response  in
          (js_response, st_opt)
  
let (js_repl_eval_js :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Util.json ->
      (FStar_Util.json * (FStar_Interactive_JsonHelper.repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun query_js  ->
      let uu____7757 = deserialize_interactive_query query_js  in
      js_repl_eval st uu____7757
  
let (js_repl_eval_str :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string * (FStar_Interactive_JsonHelper.repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun query_str  ->
      let uu____7781 =
        let uu____7791 = parse_interactive_query query_str  in
        js_repl_eval st uu____7791  in
      match uu____7781 with
      | (js_response,st_opt) ->
          let uu____7814 = FStar_Util.string_of_json js_response  in
          (uu____7814, st_opt)
  
let (js_repl_init_opts : unit -> unit) =
  fun uu____7827  ->
    let uu____7828 = FStar_Options.parse_cmd_line ()  in
    match uu____7828 with
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
              | h::uu____7851::uu____7852 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____7861 -> ()))
  
let rec (go : FStar_Interactive_JsonHelper.repl_state -> Prims.int) =
  fun st  ->
    let query =
      read_interactive_query st.FStar_Interactive_JsonHelper.repl_stdin  in
    let uu____7874 = validate_and_run_query st query  in
    match uu____7874 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
  
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref []  in
  let add_one1 e =
    let uu____7927 =
      let uu____7930 = FStar_ST.op_Bang issues  in e :: uu____7930  in
    FStar_ST.op_Colon_Equals issues uu____7927  in
  let count_errors uu____7984 =
    let uu____7985 =
      let uu____7988 = FStar_ST.op_Bang issues  in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____7988
       in
    FStar_List.length uu____7985  in
  let report uu____8023 =
    let uu____8024 = FStar_ST.op_Bang issues  in
    FStar_List.sortWith FStar_Errors.compare_issues uu____8024  in
  let clear1 uu____8055 = FStar_ST.op_Colon_Equals issues []  in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report;
    FStar_Errors.eh_clear = clear1
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
               let uu____8116 = get_json ()  in
               forward_message printer label uu____8116)
    }
  
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer  ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
  
let (initial_range : FStar_Range.range) =
  let uu____8130 = FStar_Range.mk_pos Prims.int_one Prims.int_zero  in
  let uu____8133 = FStar_Range.mk_pos Prims.int_one Prims.int_zero  in
  FStar_Range.mk_range "<input>" uu____8130 uu____8133 
let (build_initial_repl_state :
  Prims.string -> FStar_Interactive_JsonHelper.repl_state) =
  fun filename  ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps  in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range  in
    let uu____8147 = FStar_Util.open_stdin ()  in
    {
      FStar_Interactive_JsonHelper.repl_line = Prims.int_one;
      FStar_Interactive_JsonHelper.repl_column = Prims.int_zero;
      FStar_Interactive_JsonHelper.repl_fname = filename;
      FStar_Interactive_JsonHelper.repl_deps_stack = [];
      FStar_Interactive_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_Interactive_JsonHelper.repl_env = env1;
      FStar_Interactive_JsonHelper.repl_stdin = uu____8147;
      FStar_Interactive_JsonHelper.repl_names =
        FStar_Interactive_CompletionTable.empty
    }
  
let interactive_mode' :
  'Auu____8163 . FStar_Interactive_JsonHelper.repl_state -> 'Auu____8163 =
  fun init_st  ->
    write_hello ();
    (let exit_code =
       let uu____8172 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ())  in
       if uu____8172
       then
         let uu____8176 =
           let uu____8178 = FStar_Options.file_list ()  in
           FStar_List.hd uu____8178  in
         FStar_SMTEncoding_Solver.with_hints_db uu____8176
           (fun uu____8185  -> go init_st)
       else go init_st  in
     FStar_All.exit exit_code)
  
let (interactive_mode : Prims.string -> unit) =
  fun filename  ->
    install_ide_mode_hooks FStar_Interactive_JsonHelper.write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____8199 =
       let uu____8201 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____8201  in
     if uu____8199
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename  in
     let uu____8210 = FStar_Options.trace_error ()  in
     if uu____8210
     then interactive_mode' init1
     else
       (try
          (fun uu___1069_8216  ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___1068_8219 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___1068_8219)))
  