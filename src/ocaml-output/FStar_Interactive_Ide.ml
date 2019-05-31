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
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) 
  | NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
  
  | NTInclude of (FStar_Ident.lid * FStar_Ident.lid) 
  | NTBinding of (FStar_Syntax_Syntax.binding,
  FStar_TypeChecker_Env.sig_binding) FStar_Util.either 
let (uu___is_NTAlias : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTAlias _0 -> true | uu____447 -> false
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee -> match projectee with | NTAlias _0 -> _0
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTOpen _0 -> true | uu____488 -> false
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee -> match projectee with | NTOpen _0 -> _0
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTInclude _0 -> true | uu____523 -> false
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee -> match projectee with | NTInclude _0 -> _0
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTBinding _0 -> true | uu____558 -> false
let (__proj__NTBinding__item___0 :
  name_tracking_event ->
    (FStar_Syntax_Syntax.binding, FStar_TypeChecker_Env.sig_binding)
      FStar_Util.either)
  = fun projectee -> match projectee with | NTBinding _0 -> _0
let (query_of_ids :
  FStar_Ident.ident Prims.list -> FStar_Interactive_CompletionTable.query) =
  fun ids -> FStar_List.map FStar_Ident.text_of_id ids
let (query_of_lid :
  FStar_Ident.lident -> FStar_Interactive_CompletionTable.query) =
  fun lid ->
    query_of_ids
      (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident])
let (update_names_from_event :
  Prims.string ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event -> FStar_Interactive_CompletionTable.table)
  =
  fun cur_mod_str ->
    fun table ->
      fun evt ->
        let is_cur_mod lid = lid.FStar_Ident.str = cur_mod_str in
        match evt with
        | NTAlias (host, id1, included) ->
            if is_cur_mod host
            then
              let uu____626 = FStar_Ident.text_of_id id1 in
              let uu____628 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                uu____626 [] uu____628
            else table
        | NTOpen (host, (included, kind)) ->
            if is_cur_mod host
            then
              let uu____636 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____636
            else table
        | NTInclude (host, included) ->
            let uu____642 = if is_cur_mod host then [] else query_of_lid host in
            let uu____647 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____642 uu____647
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid
                  (lid, uu____659)) -> [lid]
              | FStar_Util.Inr (lids, uu____677) -> lids
              | uu____682 -> [] in
            FStar_List.fold_left
              (fun tbl ->
                 fun lid ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns in
                   let uu____699 =
                     FStar_Ident.text_of_id lid.FStar_Ident.ident in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____699 lid) table lids
let (commit_name_tracking' :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event Prims.list ->
        FStar_Interactive_CompletionTable.table)
  =
  fun cur_mod ->
    fun names1 ->
      fun name_events ->
        let cur_mod_str =
          match cur_mod with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some md ->
              let uu____730 = FStar_Syntax_Syntax.mod_name md in
              uu____730.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let (commit_name_tracking :
  FStar_JsonHelper.repl_state ->
    name_tracking_event Prims.list -> FStar_JsonHelper.repl_state)
  =
  fun st ->
    fun name_events ->
      let names1 =
        commit_name_tracking' st.FStar_JsonHelper.repl_curmod
          st.FStar_JsonHelper.repl_names name_events in
      let uu___116_756 = st in
      {
        FStar_JsonHelper.repl_line =
          (uu___116_756.FStar_JsonHelper.repl_line);
        FStar_JsonHelper.repl_column =
          (uu___116_756.FStar_JsonHelper.repl_column);
        FStar_JsonHelper.repl_fname =
          (uu___116_756.FStar_JsonHelper.repl_fname);
        FStar_JsonHelper.repl_deps_stack =
          (uu___116_756.FStar_JsonHelper.repl_deps_stack);
        FStar_JsonHelper.repl_curmod =
          (uu___116_756.FStar_JsonHelper.repl_curmod);
        FStar_JsonHelper.repl_env = (uu___116_756.FStar_JsonHelper.repl_env);
        FStar_JsonHelper.repl_stdin =
          (uu___116_756.FStar_JsonHelper.repl_stdin);
        FStar_JsonHelper.repl_names = names1
      }
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu____772 ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____786 =
        let uu____789 = FStar_ST.op_Bang events in evt :: uu____789 in
      FStar_ST.op_Colon_Equals events uu____786 in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv1 ->
             fun op ->
               let uu____850 =
                 let uu____851 =
                   let uu____856 = FStar_Syntax_DsEnv.current_module dsenv1 in
                   (uu____856, op) in
                 NTOpen uu____851 in
               push_event uu____850);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv1 ->
             fun ns ->
               let uu____862 =
                 let uu____863 =
                   let uu____868 = FStar_Syntax_DsEnv.current_module dsenv1 in
                   (uu____868, ns) in
                 NTInclude uu____863 in
               push_event uu____862);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv1 ->
             fun x ->
               fun l ->
                 let uu____876 =
                   let uu____877 =
                     let uu____884 = FStar_Syntax_DsEnv.current_module dsenv1 in
                     (uu____884, x, l) in
                   NTAlias uu____877 in
                 push_event uu____876)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____889 -> fun s -> push_event (NTBinding s))
      })
let (track_name_changes :
  env_t -> (env_t * (env_t -> (env_t * name_tracking_event Prims.list)))) =
  fun env ->
    let set_hooks dshooks tchooks env1 =
      let uu____943 =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv1 ->
             let uu____951 = FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks in
             ((), uu____951)) in
      match uu____943 with
      | ((), tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
    let uu____953 =
      let uu____958 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv in
      let uu____959 = FStar_TypeChecker_Env.tc_hooks env in
      (uu____958, uu____959) in
    match uu____953 with
    | (old_dshooks, old_tchooks) ->
        let uu____975 = fresh_name_tracking_hooks () in
        (match uu____975 with
         | (events, new_dshooks, new_tchooks) ->
             let uu____1010 = set_hooks new_dshooks new_tchooks env in
             (uu____1010,
               ((fun env1 ->
                   let uu____1024 = set_hooks old_dshooks old_tchooks env1 in
                   let uu____1025 =
                     let uu____1028 = FStar_ST.op_Bang events in
                     FStar_List.rev uu____1028 in
                   (uu____1024, uu____1025)))))
let (string_of_repl_task : FStar_JsonHelper.repl_task -> Prims.string) =
  fun uu___0_1062 ->
    match uu___0_1062 with
    | FStar_JsonHelper.LDInterleaved (intf, impl) ->
        let uu____1066 = string_of_timed_fname intf in
        let uu____1068 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1066 uu____1068
    | FStar_JsonHelper.LDSingle intf_or_impl ->
        let uu____1072 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu____1072
    | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu____1076 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1076
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
          let uu____1112 = track_name_changes st1.FStar_JsonHelper.repl_env in
          match uu____1112 with
          | (env, finish_name_tracking) ->
              let check_success uu____1157 =
                (let uu____1160 = FStar_Errors.get_err_count () in
                 uu____1160 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback) in
              let uu____1164 =
                let uu____1172 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1 ->
                       let uu____1186 =
                         FStar_PushHelper.run_repl_task
                           st1.FStar_JsonHelper.repl_curmod env1 task in
                       FStar_All.pipe_left
                         (fun _1205 -> FStar_Pervasives_Native.Some _1205)
                         uu____1186) in
                match uu____1172 with
                | FStar_Pervasives_Native.Some (curmod, env1) when
                    check_success () -> (curmod, env1, true)
                | uu____1221 ->
                    ((st1.FStar_JsonHelper.repl_curmod), env, false) in
              (match uu____1164 with
               | (curmod, env1, success) ->
                   let uu____1240 = finish_name_tracking env1 in
                   (match uu____1240 with
                    | (env2, name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___184_1261 = st1 in
                              {
                                FStar_JsonHelper.repl_line =
                                  (uu___184_1261.FStar_JsonHelper.repl_line);
                                FStar_JsonHelper.repl_column =
                                  (uu___184_1261.FStar_JsonHelper.repl_column);
                                FStar_JsonHelper.repl_fname =
                                  (uu___184_1261.FStar_JsonHelper.repl_fname);
                                FStar_JsonHelper.repl_deps_stack =
                                  (uu___184_1261.FStar_JsonHelper.repl_deps_stack);
                                FStar_JsonHelper.repl_curmod = curmod;
                                FStar_JsonHelper.repl_env = env2;
                                FStar_JsonHelper.repl_stdin =
                                  (uu___184_1261.FStar_JsonHelper.repl_stdin);
                                FStar_JsonHelper.repl_names =
                                  (uu___184_1261.FStar_JsonHelper.repl_names)
                              } in
                            commit_name_tracking st2 name_events
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
          let uu____1308 = FStar_Options.debug_any () in
          if uu____1308
          then
            let uu____1311 = string_of_repl_task task in
            FStar_Util.print2 "%s %s" verb uu____1311
          else () in
        let rec revert_many st1 uu___1_1336 =
          match uu___1_1336 with
          | [] -> st1
          | (_id, (task, _st'))::entries ->
              (debug1 "Reverting" task;
               (let st' =
                  FStar_PushHelper.pop_repl "run_repl_ls_transactions" st1 in
                let dep_graph1 =
                  FStar_TypeChecker_Env.dep_graph
                    st1.FStar_JsonHelper.repl_env in
                let st'1 =
                  let uu___210_1389 = st' in
                  let uu____1390 =
                    FStar_TypeChecker_Env.set_dep_graph
                      st'.FStar_JsonHelper.repl_env dep_graph1 in
                  {
                    FStar_JsonHelper.repl_line =
                      (uu___210_1389.FStar_JsonHelper.repl_line);
                    FStar_JsonHelper.repl_column =
                      (uu___210_1389.FStar_JsonHelper.repl_column);
                    FStar_JsonHelper.repl_fname =
                      (uu___210_1389.FStar_JsonHelper.repl_fname);
                    FStar_JsonHelper.repl_deps_stack =
                      (uu___210_1389.FStar_JsonHelper.repl_deps_stack);
                    FStar_JsonHelper.repl_curmod =
                      (uu___210_1389.FStar_JsonHelper.repl_curmod);
                    FStar_JsonHelper.repl_env = uu____1390;
                    FStar_JsonHelper.repl_stdin =
                      (uu___210_1389.FStar_JsonHelper.repl_stdin);
                    FStar_JsonHelper.repl_names =
                      (uu___210_1389.FStar_JsonHelper.repl_names)
                  } in
                revert_many st'1 entries)) in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([], []) -> FStar_Util.Inl st1
          | (task::tasks2, []) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____1443 = FStar_Options.restore_cmd_line_options false in
                FStar_All.pipe_right uu____1443 (fun a1 -> ()));
               (let timestamped_task =
                  FStar_PushHelper.update_task_timestamps task in
                let push_kind =
                  let uu____1447 = FStar_Options.lax () in
                  if uu____1447
                  then FStar_PushHelper.LaxCheck
                  else FStar_PushHelper.FullCheck in
                let uu____1452 =
                  run_repl_transaction st1 push_kind false timestamped_task in
                match uu____1452 with
                | (success, st2) ->
                    if success
                    then
                      let uu____1472 =
                        let uu___235_1473 = st2 in
                        let uu____1474 =
                          FStar_ST.op_Bang FStar_PushHelper.repl_stack in
                        {
                          FStar_JsonHelper.repl_line =
                            (uu___235_1473.FStar_JsonHelper.repl_line);
                          FStar_JsonHelper.repl_column =
                            (uu___235_1473.FStar_JsonHelper.repl_column);
                          FStar_JsonHelper.repl_fname =
                            (uu___235_1473.FStar_JsonHelper.repl_fname);
                          FStar_JsonHelper.repl_deps_stack = uu____1474;
                          FStar_JsonHelper.repl_curmod =
                            (uu___235_1473.FStar_JsonHelper.repl_curmod);
                          FStar_JsonHelper.repl_env =
                            (uu___235_1473.FStar_JsonHelper.repl_env);
                          FStar_JsonHelper.repl_stdin =
                            (uu___235_1473.FStar_JsonHelper.repl_stdin);
                          FStar_JsonHelper.repl_names =
                            (uu___235_1473.FStar_JsonHelper.repl_names)
                        } in
                      aux uu____1472 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2, prev::previous1) when
              let uu____1518 = FStar_PushHelper.update_task_timestamps task in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____1518
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2, previous1) ->
              let uu____1535 = revert_many st1 previous1 in
              aux uu____1535 tasks2 [] in
        aux st tasks (FStar_List.rev st.FStar_JsonHelper.repl_deps_stack)
let (js_pushkind : FStar_Util.json -> FStar_PushHelper.push_kind) =
  fun s ->
    let uu____1550 = FStar_JsonHelper.js_str s in
    match uu____1550 with
    | "syntax" -> FStar_PushHelper.SyntaxCheck
    | "lax" -> FStar_PushHelper.LaxCheck
    | "full" -> FStar_PushHelper.FullCheck
    | uu____1555 -> FStar_JsonHelper.js_fail "push_kind" s
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s ->
    let uu____1564 = FStar_JsonHelper.js_str s in
    match uu____1564 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____1572 -> FStar_JsonHelper.js_fail "reduction rule" s
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKCode -> true | uu____1601 -> false
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKOption _0 -> true | uu____1614 -> false
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKOption _0 -> _0
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____1642 -> false
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee -> match projectee with | CKModuleOrNamespace _0 -> _0
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1680 = FStar_JsonHelper.js_str k1 in
        (match uu____1680 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____1708 ->
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
    match projectee with | LKSymbolOnly -> true | uu____1720 -> false
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKModule -> true | uu____1731 -> false
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKOption -> true | uu____1742 -> false
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKCode -> true | uu____1753 -> false
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1766 = FStar_JsonHelper.js_str k1 in
        (match uu____1766 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____1776 ->
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
  fun projectee -> match projectee with | Exit -> true | uu____1893 -> false
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeProtocol -> true | uu____1904 -> false
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeRepl -> true | uu____1915 -> false
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Segment _0 -> true | uu____1928 -> false
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Segment _0 -> _0
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee -> match projectee with | Pop -> true | uu____1949 -> false
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Push _0 -> true | uu____1961 -> false
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | VfsAdd _0 -> true | uu____1988 -> false
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee -> match projectee with | VfsAdd _0 -> _0
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | AutoComplete _0 -> true | uu____2036 -> false
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee -> match projectee with | AutoComplete _0 -> _0
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Lookup _0 -> true | uu____2084 -> false
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee -> match projectee with | Lookup _0 -> _0
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Compute _0 -> true | uu____2154 -> false
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Compute _0 -> _0
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Search _0 -> true | uu____2201 -> false
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Search _0 -> _0
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | GenericError _0 -> true | uu____2224 -> false
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | GenericError _0 -> _0
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | ProtocolViolation _0 -> true | uu____2247 -> false
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | ProtocolViolation _0 -> _0
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee -> match projectee with | { qq; qid;_} -> qq
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee -> match projectee with | { qq; qid;_} -> qid
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___2_2285 ->
    match uu___2_2285 with
    | Exit -> false
    | DescribeProtocol -> false
    | DescribeRepl -> false
    | Segment uu____2290 -> false
    | Pop -> false
    | Push
        { push_kind = uu____2294; push_code = uu____2295;
          push_line = uu____2296; push_column = uu____2297;
          push_peek_only = false;_}
        -> false
    | VfsAdd uu____2303 -> false
    | GenericError uu____2313 -> false
    | ProtocolViolation uu____2316 -> false
    | Push uu____2319 -> true
    | AutoComplete uu____2321 -> true
    | Lookup uu____2328 -> true
    | Compute uu____2344 -> true
    | Search uu____2355 -> true
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
    match projectee with | QueryOK -> true | uu____2417 -> false
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryNOK -> true | uu____2428 -> false
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with
    | QueryViolatesProtocol -> true
    | uu____2439 -> false
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____2461 =
          let uu____2462 =
            let uu____2464 = FStar_JsonHelper.json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2464 in
          ProtocolViolation uu____2462 in
        { qq = uu____2461; qid }
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json ->
    let assoc1 errloc key a =
      let uu____2507 = FStar_JsonHelper.try_assoc key a in
      match uu____2507 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____2511 =
            let uu____2512 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            FStar_JsonHelper.InvalidQuery uu____2512 in
          FStar_Exn.raise uu____2511 in
    let request = FStar_All.pipe_right json FStar_JsonHelper.js_assoc in
    let qid =
      let uu____2532 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2532 FStar_JsonHelper.js_str in
    try
      (fun uu___348_2542 ->
         match () with
         | () ->
             let query =
               let uu____2545 = assoc1 "query" "query" request in
               FStar_All.pipe_right uu____2545 FStar_JsonHelper.js_str in
             let args =
               let uu____2557 = assoc1 "query" "args" request in
               FStar_All.pipe_right uu____2557 FStar_JsonHelper.js_assoc in
             let arg1 k = assoc1 "[args]" k args in
             let try_arg k =
               let uu____2586 = FStar_JsonHelper.try_assoc k args in
               match uu____2586 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull) ->
                   FStar_Pervasives_Native.None
               | other -> other in
             let uu____2594 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____2600 =
                     let uu____2602 = arg1 "code" in
                     FStar_All.pipe_right uu____2602 FStar_JsonHelper.js_str in
                   Segment uu____2600
               | "peek" ->
                   let uu____2606 =
                     let uu____2607 =
                       let uu____2608 = arg1 "kind" in
                       FStar_All.pipe_right uu____2608 js_pushkind in
                     let uu____2610 =
                       let uu____2612 = arg1 "code" in
                       FStar_All.pipe_right uu____2612
                         FStar_JsonHelper.js_str in
                     let uu____2615 =
                       let uu____2617 = arg1 "line" in
                       FStar_All.pipe_right uu____2617
                         FStar_JsonHelper.js_int in
                     let uu____2620 =
                       let uu____2622 = arg1 "column" in
                       FStar_All.pipe_right uu____2622
                         FStar_JsonHelper.js_int in
                     {
                       push_kind = uu____2607;
                       push_code = uu____2610;
                       push_line = uu____2615;
                       push_column = uu____2620;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____2606
               | "push" ->
                   let uu____2628 =
                     let uu____2629 =
                       let uu____2630 = arg1 "kind" in
                       FStar_All.pipe_right uu____2630 js_pushkind in
                     let uu____2632 =
                       let uu____2634 = arg1 "code" in
                       FStar_All.pipe_right uu____2634
                         FStar_JsonHelper.js_str in
                     let uu____2637 =
                       let uu____2639 = arg1 "line" in
                       FStar_All.pipe_right uu____2639
                         FStar_JsonHelper.js_int in
                     let uu____2642 =
                       let uu____2644 = arg1 "column" in
                       FStar_All.pipe_right uu____2644
                         FStar_JsonHelper.js_int in
                     {
                       push_kind = uu____2629;
                       push_code = uu____2632;
                       push_line = uu____2637;
                       push_column = uu____2642;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____2628
               | "autocomplete" ->
                   let uu____2650 =
                     let uu____2656 =
                       let uu____2658 = arg1 "partial-symbol" in
                       FStar_All.pipe_right uu____2658
                         FStar_JsonHelper.js_str in
                     let uu____2661 =
                       let uu____2662 = try_arg "context" in
                       FStar_All.pipe_right uu____2662
                         js_optional_completion_context in
                     (uu____2656, uu____2661) in
                   AutoComplete uu____2650
               | "lookup" ->
                   let uu____2670 =
                     let uu____2685 =
                       let uu____2687 = arg1 "symbol" in
                       FStar_All.pipe_right uu____2687
                         FStar_JsonHelper.js_str in
                     let uu____2690 =
                       let uu____2691 = try_arg "context" in
                       FStar_All.pipe_right uu____2691
                         js_optional_lookup_context in
                     let uu____2697 =
                       let uu____2700 =
                         let uu____2710 = try_arg "location" in
                         FStar_All.pipe_right uu____2710
                           (FStar_Util.map_option FStar_JsonHelper.js_assoc) in
                       FStar_All.pipe_right uu____2700
                         (FStar_Util.map_option
                            (fun loc ->
                               let uu____2771 =
                                 let uu____2773 =
                                   assoc1 "[location]" "filename" loc in
                                 FStar_All.pipe_right uu____2773
                                   FStar_JsonHelper.js_str in
                               let uu____2777 =
                                 let uu____2779 =
                                   assoc1 "[location]" "line" loc in
                                 FStar_All.pipe_right uu____2779
                                   FStar_JsonHelper.js_int in
                               let uu____2783 =
                                 let uu____2785 =
                                   assoc1 "[location]" "column" loc in
                                 FStar_All.pipe_right uu____2785
                                   FStar_JsonHelper.js_int in
                               (uu____2771, uu____2777, uu____2783))) in
                     let uu____2792 =
                       let uu____2796 = arg1 "requested-info" in
                       FStar_All.pipe_right uu____2796
                         (FStar_JsonHelper.js_list FStar_JsonHelper.js_str) in
                     (uu____2685, uu____2690, uu____2697, uu____2792) in
                   Lookup uu____2670
               | "compute" ->
                   let uu____2809 =
                     let uu____2819 =
                       let uu____2821 = arg1 "term" in
                       FStar_All.pipe_right uu____2821
                         FStar_JsonHelper.js_str in
                     let uu____2824 =
                       let uu____2829 = try_arg "rules" in
                       FStar_All.pipe_right uu____2829
                         (FStar_Util.map_option
                            (FStar_JsonHelper.js_list js_reductionrule)) in
                     (uu____2819, uu____2824) in
                   Compute uu____2809
               | "search" ->
                   let uu____2847 =
                     let uu____2849 = arg1 "terms" in
                     FStar_All.pipe_right uu____2849 FStar_JsonHelper.js_str in
                   Search uu____2847
               | "vfs-add" ->
                   let uu____2853 =
                     let uu____2862 =
                       let uu____2866 = try_arg "filename" in
                       FStar_All.pipe_right uu____2866
                         (FStar_Util.map_option FStar_JsonHelper.js_str) in
                     let uu____2876 =
                       let uu____2878 = arg1 "contents" in
                       FStar_All.pipe_right uu____2878
                         FStar_JsonHelper.js_str in
                     (uu____2862, uu____2876) in
                   VfsAdd uu____2853
               | uu____2885 ->
                   let uu____2887 =
                     FStar_Util.format1 "Unknown query '%s'" query in
                   ProtocolViolation uu____2887 in
             { qq = uu____2594; qid }) ()
    with
    | FStar_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure qid expected got
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query ->
    try
      (fun uu___383_2906 ->
         match () with | () -> unpack_interactive_query js_query) ()
    with
    | FStar_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid = "?" }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure "?" expected got
let (parse_interactive_query : Prims.string -> query) =
  fun query_str ->
    let uu____2926 = FStar_Util.json_of_string query_str in
    match uu____2926 with
    | FStar_Pervasives_Native.None ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream ->
    let uu____2938 = FStar_Util.read_line stream in
    match uu____2938 with
    | FStar_Pervasives_Native.None -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
let json_of_opt :
  'Auu____2954 .
    ('Auu____2954 -> FStar_Util.json) ->
      'Auu____2954 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a ->
    fun opt_a ->
      let uu____2974 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2974
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
    let uu____2994 =
      let uu____3002 =
        let uu____3010 =
          let uu____3018 =
            let uu____3024 =
              let uu____3025 =
                let uu____3028 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____3034 = FStar_Range.json_of_use_range r in
                      [uu____3034] in
                let uu____3035 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____3041 = FStar_Range.def_range r in
                      let uu____3042 = FStar_Range.use_range r in
                      uu____3041 <> uu____3042 ->
                      let uu____3043 = FStar_Range.json_of_def_range r in
                      [uu____3043]
                  | uu____3044 -> [] in
                FStar_List.append uu____3028 uu____3035 in
              FStar_Util.JsonList uu____3025 in
            ("ranges", uu____3024) in
          [uu____3018] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____3010 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____3002 in
    FStar_Util.JsonAssoc uu____2994
let (alist_of_symbol_lookup_result :
  FStar_QueryHelper.sl_reponse -> (Prims.string * FStar_Util.json) Prims.list)
  =
  fun lr ->
    let uu____3086 =
      let uu____3094 =
        let uu____3100 =
          json_of_opt FStar_Range.json_of_def_range
            lr.FStar_QueryHelper.slr_def_range in
        ("defined-at", uu____3100) in
      let uu____3103 =
        let uu____3111 =
          let uu____3117 =
            json_of_opt (fun _3119 -> FStar_Util.JsonStr _3119)
              lr.FStar_QueryHelper.slr_typ in
          ("type", uu____3117) in
        let uu____3122 =
          let uu____3130 =
            let uu____3136 =
              json_of_opt (fun _3138 -> FStar_Util.JsonStr _3138)
                lr.FStar_QueryHelper.slr_doc in
            ("documentation", uu____3136) in
          let uu____3141 =
            let uu____3149 =
              let uu____3155 =
                json_of_opt (fun _3157 -> FStar_Util.JsonStr _3157)
                  lr.FStar_QueryHelper.slr_def in
              ("definition", uu____3155) in
            [uu____3149] in
          uu____3130 :: uu____3141 in
        uu____3111 :: uu____3122 in
      uu____3094 :: uu____3103 in
    ("name", (FStar_Util.JsonStr (lr.FStar_QueryHelper.slr_name))) ::
      uu____3086
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3202 =
      FStar_List.map (fun _3206 -> FStar_Util.JsonStr _3206)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _3209 -> FStar_Util.JsonList _3209) uu____3202 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptSet -> true | uu____3238 -> false
let (uu___is_OptReset : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReset -> true | uu____3249 -> false
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReadOnly -> true | uu____3260 -> false
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___3_3268 ->
    match uu___3_3268 with
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
  fun uu___4_3519 ->
    match uu___4_3519 with
    | FStar_Options.Const uu____3521 -> "flag"
    | FStar_Options.IntStr uu____3523 -> "int"
    | FStar_Options.BoolStr -> "bool"
    | FStar_Options.PathStr uu____3527 -> "path"
    | FStar_Options.SimpleStr uu____3530 -> "string"
    | FStar_Options.EnumStr uu____3533 -> "enum"
    | FStar_Options.OpenEnumStr uu____3538 -> "open enum"
    | FStar_Options.PostProcessed (uu____3548, typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____3558, typ) ->
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
        | FStar_Options.Const uu____3630 -> [""]
        | FStar_Options.BoolStr -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs, desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____3668, elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____3678, elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____3686 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____3686
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___5_3697 ->
    match uu___5_3697 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____3709 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____3709
    | FStar_Options.Unset -> FStar_Util.JsonNull
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt ->
    let uu____3725 =
      let uu____3733 =
        let uu____3741 =
          let uu____3747 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____3747) in
        let uu____3750 =
          let uu____3758 =
            let uu____3764 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____3764) in
          let uu____3767 =
            let uu____3775 =
              let uu____3781 =
                json_of_opt (fun _3783 -> FStar_Util.JsonStr _3783)
                  opt.opt_documentation in
              ("documentation", uu____3781) in
            let uu____3786 =
              let uu____3794 =
                let uu____3800 =
                  let uu____3801 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____3801 in
                ("type", uu____3800) in
              [uu____3794;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____3775 :: uu____3786 in
          uu____3758 :: uu____3767 in
        uu____3741 :: uu____3750 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____3733 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3725
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt ->
    let uu____3857 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____3857
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
      let uu____3953 =
        let uu____3961 =
          let uu____3969 =
            let uu____3975 =
              let uu____3976 = FStar_ST.op_Bang repl_current_qid in
              json_of_opt (fun _4006 -> FStar_Util.JsonStr _4006) uu____3976 in
            ("query-id", uu____3975) in
          [uu____3969;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)] in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____3961 in
      FStar_Util.JsonAssoc uu____3953
let forward_message :
  'Auu____4050 .
    (FStar_Util.json -> 'Auu____4050) ->
      Prims.string -> FStar_Util.json -> 'Auu____4050
  =
  fun callback ->
    fun level ->
      fun contents ->
        let uu____4073 = json_of_message level contents in
        callback uu____4073
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____4077 =
      FStar_List.map (fun _4081 -> FStar_Util.JsonStr _4081)
        interactive_protocol_features in
    FStar_Util.JsonList uu____4077 in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
let (write_hello : unit -> unit) =
  fun uu____4095 -> FStar_JsonHelper.write_json json_of_hello
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name ->
    fun typ ->
      let flag = Prims.op_Hat "--" name in
      let uu____4113 = FStar_Options.desc_of_opt_type typ in
      match uu____4113 with
      | FStar_Pervasives_Native.None -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____4129 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____4164 ->
            match uu____4164 with
            | (_shortname, name, typ, doc1) ->
                let uu____4188 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____4188
                  (FStar_Util.map_option
                     (fun default_value ->
                        let uu____4200 = sig_of_fstar_option name typ in
                        let uu____4202 = snippets_of_fstar_option name typ in
                        let uu____4206 =
                          let uu____4207 = FStar_Options.settable name in
                          if uu____4207
                          then OptSet
                          else
                            (let uu____4212 = FStar_Options.resettable name in
                             if uu____4212 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____4200;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____4202;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____4206
                        })))) in
  FStar_All.pipe_right uu____4129
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
    let uu___555_4251 = opt in
    let uu____4252 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___555_4251.opt_name);
      opt_sig = (uu___555_4251.opt_sig);
      opt_value = uu____4252;
      opt_default = (uu___555_4251.opt_default);
      opt_type = (uu___555_4251.opt_type);
      opt_snippets = (uu___555_4251.opt_snippets);
      opt_documentation = (uu___555_4251.opt_documentation);
      opt_permission_level = (uu___555_4251.opt_permission_level)
    }
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1 ->
    let uu____4268 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____4268
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____4295 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____4295)
    else ("", opt_name)
let (json_of_repl_state : FStar_JsonHelper.repl_state -> FStar_Util.json) =
  fun st ->
    let filenames uu____4326 =
      match uu____4326 with
      | (uu____4338, (task, uu____4340)) ->
          (match task with
           | FStar_JsonHelper.LDInterleaved (intf, impl) ->
               [intf.FStar_JsonHelper.tf_fname;
               impl.FStar_JsonHelper.tf_fname]
           | FStar_JsonHelper.LDSingle intf_or_impl ->
               [intf_or_impl.FStar_JsonHelper.tf_fname]
           | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
               [intf.FStar_JsonHelper.tf_fname]
           | uu____4359 -> []) in
    let uu____4361 =
      let uu____4369 =
        let uu____4375 =
          let uu____4376 =
            let uu____4379 =
              FStar_List.concatMap filenames
                st.FStar_JsonHelper.repl_deps_stack in
            FStar_List.map (fun _4393 -> FStar_Util.JsonStr _4393) uu____4379 in
          FStar_Util.JsonList uu____4376 in
        ("loaded-dependencies", uu____4375) in
      let uu____4396 =
        let uu____4404 =
          let uu____4410 =
            let uu____4411 =
              let uu____4414 = current_fstar_options (fun uu____4419 -> true) in
              FStar_List.map json_of_fstar_option uu____4414 in
            FStar_Util.JsonList uu____4411 in
          ("options", uu____4410) in
        [uu____4404] in
      uu____4369 :: uu____4396 in
    FStar_Util.JsonAssoc uu____4361
let run_exit :
  'Auu____4445 'Auu____4446 .
    'Auu____4445 ->
      ((query_status * FStar_Util.json) * ('Auu____4446, Prims.int)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol :
  'Auu____4483 'Auu____4484 .
    'Auu____4483 ->
      ((query_status * FStar_Util.json) * ('Auu____4483, 'Auu____4484)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl :
  'Auu____4515 .
    FStar_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
        'Auu____4515) FStar_Util.either)
  =
  fun st ->
    let uu____4533 =
      let uu____4538 = json_of_repl_state st in (QueryOK, uu____4538) in
    (uu____4533, (FStar_Util.Inl st))
let run_protocol_violation :
  'Auu____4556 'Auu____4557 .
    'Auu____4556 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____4556, 'Auu____4557)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error :
  'Auu____4599 'Auu____4600 .
    'Auu____4599 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____4599, 'Auu____4600)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____4640 ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_segment :
  'Auu____4652 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____4652) FStar_Util.either)
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
      let collect_decls uu____4688 =
        let uu____4689 = FStar_Parser_Driver.parse_fragment frag in
        match uu____4689 with
        | FStar_Parser_Driver.Empty -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____4695, decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____4701, decls, uu____4703)) -> decls in
      let uu____4710 =
        with_captured_errors st.FStar_JsonHelper.repl_env
          FStar_Util.sigint_ignore
          (fun uu____4719 ->
             let uu____4720 = collect_decls () in
             FStar_All.pipe_left
               (fun _4731 -> FStar_Pervasives_Native.Some _4731) uu____4720) in
      match uu____4710 with
      | FStar_Pervasives_Native.None ->
          let errors =
            let uu____4749 = collect_errors () in
            FStar_All.pipe_right uu____4749 (FStar_List.map json_of_issue) in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____4775 =
              let uu____4783 =
                let uu____4789 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl) in
                ("def_range", uu____4789) in
              [uu____4783] in
            FStar_Util.JsonAssoc uu____4775 in
          let js_decls =
            let uu____4803 = FStar_List.map json_of_decl decls in
            FStar_All.pipe_left (fun _4808 -> FStar_Util.JsonList _4808)
              uu____4803 in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
let run_vfs_add :
  'Auu____4838 .
    FStar_JsonHelper.repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
            'Auu____4838) FStar_Util.either)
  =
  fun st ->
    fun opt_fname ->
      fun contents ->
        let fname = FStar_Util.dflt st.FStar_JsonHelper.repl_fname opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop :
  'Auu____4891 .
    FStar_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
        'Auu____4891) FStar_Util.either)
  =
  fun st ->
    let uu____4909 = nothing_left_to_pop st in
    if uu____4909
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
      let uu____4996 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents) in
      FStar_JsonHelper.write_json uu____4996
let (write_repl_ld_task_progress : FStar_JsonHelper.repl_task -> unit) =
  fun task ->
    match task with
    | FStar_JsonHelper.LDInterleaved (uu____5004, tf) ->
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
    | uu____5056 -> ()
let (load_deps :
  FStar_JsonHelper.repl_state ->
    ((FStar_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st ->
    let uu____5074 =
      with_captured_errors st.FStar_JsonHelper.repl_env
        FStar_Util.sigint_ignore
        (fun _env ->
           let uu____5102 =
             FStar_PushHelper.deps_and_repl_ld_tasks_of_our_file
               st.FStar_JsonHelper.repl_fname in
           FStar_All.pipe_left
             (fun _5149 -> FStar_Pervasives_Native.Some _5149) uu____5102) in
    match uu____5074 with
    | FStar_Pervasives_Native.None -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) ->
        let st1 =
          let uu___645_5204 = st in
          let uu____5205 =
            FStar_TypeChecker_Env.set_dep_graph st.FStar_JsonHelper.repl_env
              dep_graph1 in
          {
            FStar_JsonHelper.repl_line =
              (uu___645_5204.FStar_JsonHelper.repl_line);
            FStar_JsonHelper.repl_column =
              (uu___645_5204.FStar_JsonHelper.repl_column);
            FStar_JsonHelper.repl_fname =
              (uu___645_5204.FStar_JsonHelper.repl_fname);
            FStar_JsonHelper.repl_deps_stack =
              (uu___645_5204.FStar_JsonHelper.repl_deps_stack);
            FStar_JsonHelper.repl_curmod =
              (uu___645_5204.FStar_JsonHelper.repl_curmod);
            FStar_JsonHelper.repl_env = uu____5205;
            FStar_JsonHelper.repl_stdin =
              (uu___645_5204.FStar_JsonHelper.repl_stdin);
            FStar_JsonHelper.repl_names =
              (uu___645_5204.FStar_JsonHelper.repl_names)
          } in
        let uu____5206 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress in
        (match uu____5206 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue ->
    let uu___655_5261 = issue in
    let uu____5262 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____5262;
      FStar_Errors.issue_level = (uu___655_5261.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___655_5261.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___655_5261.FStar_Errors.issue_number)
    }
let run_push_without_deps :
  'Auu____5272 .
    FStar_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____5272) FStar_Util.either)
  =
  fun st ->
    fun query ->
      let set_nosynth_flag st1 flag =
        let uu___662_5308 = st1 in
        {
          FStar_JsonHelper.repl_line =
            (uu___662_5308.FStar_JsonHelper.repl_line);
          FStar_JsonHelper.repl_column =
            (uu___662_5308.FStar_JsonHelper.repl_column);
          FStar_JsonHelper.repl_fname =
            (uu___662_5308.FStar_JsonHelper.repl_fname);
          FStar_JsonHelper.repl_deps_stack =
            (uu___662_5308.FStar_JsonHelper.repl_deps_stack);
          FStar_JsonHelper.repl_curmod =
            (uu___662_5308.FStar_JsonHelper.repl_curmod);
          FStar_JsonHelper.repl_env =
            (let uu___664_5310 = st1.FStar_JsonHelper.repl_env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___664_5310.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___664_5310.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___664_5310.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___664_5310.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___664_5310.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___664_5310.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___664_5310.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___664_5310.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___664_5310.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___664_5310.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___664_5310.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___664_5310.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___664_5310.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___664_5310.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___664_5310.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___664_5310.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___664_5310.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___664_5310.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___664_5310.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___664_5310.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___664_5310.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___664_5310.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___664_5310.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___664_5310.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___664_5310.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___664_5310.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___664_5310.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___664_5310.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___664_5310.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___664_5310.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___664_5310.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___664_5310.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___664_5310.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___664_5310.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___664_5310.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___664_5310.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___664_5310.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___664_5310.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___664_5310.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___664_5310.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___664_5310.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___664_5310.FStar_TypeChecker_Env.nbe)
             });
          FStar_JsonHelper.repl_stdin =
            (uu___662_5308.FStar_JsonHelper.repl_stdin);
          FStar_JsonHelper.repl_names =
            (uu___662_5308.FStar_JsonHelper.repl_names)
        } in
      let uu____5311 = query in
      match uu____5311 with
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
            let uu____5338 =
              run_repl_transaction st1 push_kind peek_only
                (FStar_JsonHelper.PushFragment frag) in
            match uu____5338 with
            | (success, st2) ->
                let st3 = set_nosynth_flag st2 false in
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu____5367 =
                    let uu____5370 = collect_errors () in
                    FStar_All.pipe_right uu____5370
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu____5367 in
                let st4 =
                  if success
                  then
                    let uu___683_5379 = st3 in
                    {
                      FStar_JsonHelper.repl_line = line;
                      FStar_JsonHelper.repl_column = column;
                      FStar_JsonHelper.repl_fname =
                        (uu___683_5379.FStar_JsonHelper.repl_fname);
                      FStar_JsonHelper.repl_deps_stack =
                        (uu___683_5379.FStar_JsonHelper.repl_deps_stack);
                      FStar_JsonHelper.repl_curmod =
                        (uu___683_5379.FStar_JsonHelper.repl_curmod);
                      FStar_JsonHelper.repl_env =
                        (uu___683_5379.FStar_JsonHelper.repl_env);
                      FStar_JsonHelper.repl_stdin =
                        (uu___683_5379.FStar_JsonHelper.repl_stdin);
                      FStar_JsonHelper.repl_names =
                        (uu___683_5379.FStar_JsonHelper.repl_names)
                    }
                  else st3 in
                ((status, json_errors), (FStar_Util.Inl st4))))
let run_push_with_deps :
  'Auu____5397 .
    FStar_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____5397) FStar_Util.either)
  =
  fun st ->
    fun query ->
      (let uu____5421 = FStar_Options.debug_any () in
       if uu____5421
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.FStar_JsonHelper.repl_env false;
      (let uu____5429 = load_deps st in
       match uu____5429 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____5464 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu____5464 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1, deps) ->
           ((let uu____5498 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____5498 (fun a2 -> ()));
            (let names1 =
               FStar_PushHelper.add_module_completions
                 st1.FStar_JsonHelper.repl_fname deps
                 st1.FStar_JsonHelper.repl_names in
             run_push_without_deps
               (let uu___701_5502 = st1 in
                {
                  FStar_JsonHelper.repl_line =
                    (uu___701_5502.FStar_JsonHelper.repl_line);
                  FStar_JsonHelper.repl_column =
                    (uu___701_5502.FStar_JsonHelper.repl_column);
                  FStar_JsonHelper.repl_fname =
                    (uu___701_5502.FStar_JsonHelper.repl_fname);
                  FStar_JsonHelper.repl_deps_stack =
                    (uu___701_5502.FStar_JsonHelper.repl_deps_stack);
                  FStar_JsonHelper.repl_curmod =
                    (uu___701_5502.FStar_JsonHelper.repl_curmod);
                  FStar_JsonHelper.repl_env =
                    (uu___701_5502.FStar_JsonHelper.repl_env);
                  FStar_JsonHelper.repl_stdin =
                    (uu___701_5502.FStar_JsonHelper.repl_stdin);
                  FStar_JsonHelper.repl_names = names1
                }) query)))
let run_push :
  'Auu____5510 .
    FStar_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____5510) FStar_Util.either)
  =
  fun st ->
    fun query ->
      let uu____5533 = nothing_left_to_pop st in
      if uu____5533
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
          let uu____5600 =
            FStar_QueryHelper.symlookup st.FStar_JsonHelper.repl_env symbol
              pos_opt requested_info in
          match uu____5600 with
          | FStar_Pervasives_Native.None -> FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some result ->
              let uu____5635 =
                let uu____5648 = alist_of_symbol_lookup_result result in
                ("symbol", uu____5648) in
              FStar_Util.Inr uu____5635
let (run_option_lookup :
  Prims.string ->
    (Prims.string,
      (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
      FStar_Util.either)
  =
  fun opt_name ->
    let uu____5703 = trim_option_name opt_name in
    match uu____5703 with
    | (uu____5727, trimmed_name) ->
        let uu____5733 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____5733 with
         | FStar_Pervasives_Native.None ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____5768 =
               let uu____5781 =
                 let uu____5789 = update_option opt in
                 alist_of_fstar_option uu____5789 in
               ("option", uu____5781) in
             FStar_Util.Inr uu____5768)
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
      let uu____5847 =
        FStar_Interactive_CompletionTable.find_module_or_ns
          st.FStar_JsonHelper.repl_names query in
      match uu____5847 with
      | FStar_Pervasives_Native.None ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____5882 =
            let uu____5895 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____5895) in
          FStar_Util.Inr uu____5882
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____5926 =
            let uu____5939 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____5939) in
          FStar_Util.Inr uu____5926
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
          let uu____6019 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____6019 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____6093 ->
              let uu____6108 = run_module_lookup st symbol in
              (match uu____6108 with
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
  'Auu____6296 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        lookup_context ->
          FStar_QueryHelper.position FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) *
                (FStar_JsonHelper.repl_state, 'Auu____6296)
                FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun context ->
        fun pos_opt ->
          fun requested_info ->
            let uu____6346 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____6346 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind, info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let run_code_autocomplete :
  'Auu____6452 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____6452) FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      let result = FStar_QueryHelper.ck_completion st search_term in
      let js =
        FStar_List.map
          FStar_Interactive_CompletionTable.json_of_completion_result result in
      ((QueryOK, (FStar_Util.JsonList js)), (FStar_Util.Inl st))
let run_module_autocomplete :
  'Auu____6506 'Auu____6507 'Auu____6508 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        'Auu____6506 ->
          'Auu____6507 ->
            ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
              'Auu____6508) FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun modules1 ->
        fun namespaces ->
          let needle = FStar_Util.split search_term "." in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.FStar_JsonHelper.repl_names needle
              (fun _6555 -> FStar_Pervasives_Native.Some _6555) in
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
        let uu____6589 =
          match opt.opt_permission_level with
          | OptSet -> (true, "")
          | OptReset -> (is_reset, "#reset-only")
          | OptReadOnly -> (false, "read-only") in
        match uu____6589 with
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
  'Auu____6652 'Auu____6653 .
    'Auu____6652 ->
      Prims.string ->
        Prims.bool ->
          ((query_status * FStar_Util.json) * ('Auu____6652, 'Auu____6653)
            FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun is_reset ->
        let uu____6685 = trim_option_name search_term in
        match uu____6685 with
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
        | (uu____6741, uu____6742) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete :
  'Auu____6765 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
            'Auu____6765) FStar_Util.either)
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
  'Auu____6816 'Auu____6817 .
    FStar_JsonHelper.repl_state ->
      'Auu____6816 ->
        (FStar_JsonHelper.repl_state -> 'Auu____6816) ->
          ('Auu____6816 * (FStar_JsonHelper.repl_state, 'Auu____6817)
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
            (fun uu___817_6858 ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____6869 ->
                        let uu____6870 = task st1 in
                        FStar_All.pipe_left
                          (fun _6875 -> FStar_Util.Inl _6875) uu____6870)) ()
          with | FStar_Util.SigInt -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e in
        let st2 = FStar_PushHelper.pop_repl "run_and_rewind" st1 in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
let run_with_parsed_and_tc_term :
  'Auu____6924 'Auu____6925 'Auu____6926 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        'Auu____6924 ->
          'Auu____6925 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) *
                (FStar_JsonHelper.repl_state, 'Auu____6926)
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
                    ((uu____7028,
                      { FStar_Syntax_Syntax.lbname = uu____7029;
                        FStar_Syntax_Syntax.lbunivs = univs1;
                        FStar_Syntax_Syntax.lbtyp = uu____7031;
                        FStar_Syntax_Syntax.lbeff = uu____7032;
                        FStar_Syntax_Syntax.lbdef = def;
                        FStar_Syntax_Syntax.lbattrs = uu____7034;
                        FStar_Syntax_Syntax.lbpos = uu____7035;_}::[]),
                     uu____7036);
                  FStar_Syntax_Syntax.sigrng = uu____7037;
                  FStar_Syntax_Syntax.sigquals = uu____7038;
                  FStar_Syntax_Syntax.sigmeta = uu____7039;
                  FStar_Syntax_Syntax.sigattrs = uu____7040;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____7079 -> FStar_Pervasives_Native.None in
            let parse1 frag =
              let uu____7100 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag) in
              match uu____7100 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls, uu____7106) ->
                  FStar_Pervasives_Native.Some decls
              | uu____7127 -> FStar_Pervasives_Native.None in
            let desugar env decls =
              let uu____7145 =
                let uu____7150 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
                uu____7150 env.FStar_TypeChecker_Env.dsenv in
              FStar_Pervasives_Native.fst uu____7145 in
            let typecheck tcenv decls =
              let uu____7172 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
              match uu____7172 with | (ses, uu____7186, uu____7187) -> ses in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1 ->
                 let tcenv = st1.FStar_JsonHelper.repl_env in
                 let frag = dummy_let_fragment term in
                 let uu____7208 = parse1 frag in
                 match uu____7208 with
                 | FStar_Pervasives_Native.None ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____7234 =
                       let decls1 = desugar tcenv decls in
                       let ses = typecheck tcenv decls1 in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1, def) ->
                           let uu____7270 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def in
                           (match uu____7270 with
                            | (univs2, def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2 in
                                continuation tcenv1 def1) in
                     let uu____7282 = FStar_Options.trace_error () in
                     if uu____7282
                     then aux ()
                     else
                       (try
                          (fun uu___900_7296 -> match () with | () -> aux ())
                            ()
                        with
                        | uu___899_7305 ->
                            let uu____7310 =
                              FStar_Errors.issue_of_exn uu___899_7305 in
                            (match uu____7310 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____7318 =
                                   let uu____7319 =
                                     FStar_Errors.format_issue issue in
                                   FStar_Util.JsonStr uu____7319 in
                                 (QueryNOK, uu____7318)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Exn.raise uu___899_7305)))
let run_compute :
  'Auu____7334 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
            'Auu____7334) FStar_Util.either)
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
               let uu____7412 =
                 let uu____7413 =
                   FStar_QueryHelper.term_to_string tcenv normalized in
                 FStar_Util.JsonStr uu____7413 in
               (QueryOK, uu____7412))
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NameContainsStr _0 -> true | uu____7448 -> false
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee -> match projectee with | NameContainsStr _0 -> _0
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeContainsLid _0 -> true | uu____7470 -> false
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TypeContainsLid _0 -> _0
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | { st_negate; st_term;_} -> st_negate
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee -> match projectee with | { st_negate; st_term;_} -> st_term
let (st_cost : search_term' -> Prims.int) =
  fun uu___6_7505 ->
    match uu___6_7505 with
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
    let uu____7639 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____7646 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____7639; sc_fvars = uu____7646 }
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv ->
    fun sc ->
      let uu____7670 = FStar_ST.op_Bang sc.sc_typ in
      match uu____7670 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let typ =
            let uu____7698 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____7698 with
            | FStar_Pervasives_Native.None ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7717, typ), uu____7719) ->
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
      let uu____7769 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____7769 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None ->
          let fv =
            let uu____7813 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____7813 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv ->
    fun sc ->
      let typ_str =
        let uu____7857 = sc_typ tcenv sc in
        FStar_QueryHelper.term_to_string tcenv uu____7857 in
      let uu____7858 =
        let uu____7866 =
          let uu____7872 =
            let uu____7873 =
              let uu____7875 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              uu____7875.FStar_Ident.str in
            FStar_Util.JsonStr uu____7873 in
          ("lid", uu____7872) in
        [uu____7866; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu____7858
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidSearch uu____7908 -> true
    | uu____7911 -> false
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidSearch uu____7921 -> uu____7921
let run_search :
  'Auu____7930 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____7930) FStar_Util.either)
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
              let uu____7977 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____7977 in
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
              let uu____8036 =
                let uu____8037 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____8037 in
              FStar_Exn.raise uu____8036
            else
              if beg_quote
              then
                (let uu____8043 = strip_quotes term1 in
                 NameContainsStr uu____8043)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____8048 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu____8048 with
                 | FStar_Pervasives_Native.None ->
                     let uu____8051 =
                       let uu____8052 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____8052 in
                     FStar_Exn.raise uu____8051
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____8080 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____8080 in
      let results =
        try
          (fun uu___1013_8114 ->
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
                        let uu____8162 = FStar_List.map pprint_one terms in
                        FStar_Util.concat_l " " uu____8162 in
                      let uu____8168 =
                        let uu____8169 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds in
                        InvalidSearch uu____8169 in
                      FStar_Exn.raise uu____8168
                  | uu____8176 -> (QueryOK, (FStar_Util.JsonList js)))) ()
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
          { push_kind = FStar_PushHelper.SyntaxCheck; push_code = uu____8307;
            push_line = uu____8308; push_column = uu____8309;
            push_peek_only = false;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____8315 ->
          (match st.FStar_JsonHelper.repl_curmod with
           | FStar_Pervasives_Native.None when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____8317 -> q)
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
      let uu____8390 = validate_and_run_query st query in
      match uu____8390 with
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
      let uu____8456 = deserialize_interactive_query query_js in
      js_repl_eval st uu____8456
let (js_repl_eval_str :
  FStar_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string * (FStar_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query_str ->
      let uu____8480 =
        let uu____8490 = parse_interactive_query query_str in
        js_repl_eval st uu____8490 in
      match uu____8480 with
      | (js_response, st_opt) ->
          let uu____8513 = FStar_Util.string_of_json js_response in
          (uu____8513, st_opt)
let (js_repl_init_opts : unit -> unit) =
  fun uu____8526 ->
    let uu____8527 = FStar_Options.parse_cmd_line () in
    match uu____8527 with
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
              | h::uu____8550::uu____8551 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____8560 -> ()))
let rec (go : FStar_JsonHelper.repl_state -> Prims.int) =
  fun st ->
    let query = read_interactive_query st.FStar_JsonHelper.repl_stdin in
    let uu____8573 = validate_and_run_query st query in
    match uu____8573 with
    | ((status, response), state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____8626 =
      let uu____8629 = FStar_ST.op_Bang issues in e :: uu____8629 in
    FStar_ST.op_Colon_Equals issues uu____8626 in
  let count_errors uu____8683 =
    let uu____8684 =
      let uu____8687 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____8687 in
    FStar_List.length uu____8684 in
  let report uu____8722 =
    let uu____8723 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____8723 in
  let clear1 uu____8754 = FStar_ST.op_Colon_Equals issues [] in
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
               let uu____8815 = get_json () in
               forward_message printer label uu____8815)
    }
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
let (initial_range : Prims.string -> FStar_Range.range) =
  fun fname ->
    let uu____8836 =
      FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
    let uu____8839 =
      FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
    FStar_Range.mk_range fname uu____8836 uu____8839
let (build_initial_repl_state : Prims.string -> FStar_JsonHelper.repl_state)
  =
  fun filename ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
    let env1 =
      let uu____8852 = initial_range filename in
      FStar_TypeChecker_Env.set_range env uu____8852 in
    let uu____8853 = FStar_Util.open_stdin () in
    {
      FStar_JsonHelper.repl_line = (Prims.parse_int "1");
      FStar_JsonHelper.repl_column = (Prims.parse_int "0");
      FStar_JsonHelper.repl_fname = filename;
      FStar_JsonHelper.repl_deps_stack = [];
      FStar_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_JsonHelper.repl_env = env1;
      FStar_JsonHelper.repl_stdin = uu____8853;
      FStar_JsonHelper.repl_names = FStar_Interactive_CompletionTable.empty
    }
let interactive_mode' :
  'Auu____8869 . FStar_JsonHelper.repl_state -> 'Auu____8869 =
  fun init_st ->
    write_hello ();
    (let exit_code =
       let uu____8878 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu____8878
       then
         let uu____8882 =
           let uu____8884 = FStar_Options.file_list () in
           FStar_List.hd uu____8884 in
         FStar_SMTEncoding_Solver.with_hints_db uu____8882
           (fun uu____8891 -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let (interactive_mode : Prims.string -> unit) =
  fun filename ->
    install_ide_mode_hooks FStar_JsonHelper.write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____8905 =
       let uu____8907 = FStar_Options.codegen () in
       FStar_Option.isSome uu____8907 in
     if uu____8905
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename in
     let uu____8916 = FStar_Options.trace_error () in
     if uu____8916
     then interactive_mode' init1
     else
       (try
          (fun uu___1162_8922 ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___1161_8925 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___1161_8925)))