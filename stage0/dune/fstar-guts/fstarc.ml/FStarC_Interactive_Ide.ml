open Prims
let dbg : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "IDE"
let json_of_issue : FStarC_Errors.issue -> FStarC_Json.json=
  FStarC_Interactive_Ide_Types.json_of_issue
let with_captured_errors' (env : FStarC_TypeChecker_Env.env_t)
  (sigint_handler : FStarC_Util.sigint_handler)
  (f : FStarC_TypeChecker_Env.env_t -> 'uuuuu FStar_Pervasives_Native.option)
  : 'uuuuu FStar_Pervasives_Native.option=
  try
    (fun uu___ ->
       match () with
       | () ->
           FStarC_Util.with_sigint_handler sigint_handler
             (fun uu___1 -> f env)) ()
  with
  | FStarC_Effect.Failure msg ->
      let msg1 =
        Prims.strcat "ASSERTION FAILURE: "
          (Prims.strcat msg
             "\nF* may be in an inconsistent state.\nPlease file a bug report, ideally with a minimized version of the program that triggered the error.") in
      (FStarC_Errors.log_issue FStarC_TypeChecker_Env.hasRange_env env
         FStarC_Errors_Codes.Error_IDEAssertionFailure ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic msg1);
       FStar_Pervasives_Native.None)
  | FStarC_Util.SigInt ->
      (FStarC_Format.print_string "Interrupted"; FStar_Pervasives_Native.None)
  | FStarC_Errors.Error e ->
      (FStarC_Errors.add_errors [e]; FStar_Pervasives_Native.None)
  | FStarC_Errors.Stop -> FStar_Pervasives_Native.None
let with_captured_errors (env : FStarC_TypeChecker_Env.env_t)
  (sigint_handler : FStarC_Util.sigint_handler)
  (f : FStarC_TypeChecker_Env.env_t -> 'uuuuu FStar_Pervasives_Native.option)
  : 'uuuuu FStar_Pervasives_Native.option=
  let uu___ = FStarC_Options.trace_error () in
  if uu___ then f env else with_captured_errors' env sigint_handler f
type env_t = FStarC_TypeChecker_Env.env
let repl_current_qid :
  Prims.string FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let nothing_left_to_pop (st : FStarC_Interactive_Ide_Types.repl_state) :
  Prims.bool=
  let uu___ =
    let uu___1 =
      FStarC_Effect.op_Bang FStarC_Interactive_PushHelper.repl_stack in
    FStarC_List.length uu___1 in
  uu___ =
    (FStarC_List.length st.FStarC_Interactive_Ide_Types.repl_deps_stack)
let run_repl_transaction (st : FStarC_Interactive_Ide_Types.repl_state)
  (push_kind :
    FStarC_Interactive_Ide_Types.push_kind FStar_Pervasives_Native.option)
  (must_rollback : Prims.bool)
  (task : FStarC_Interactive_Ide_Types.repl_task) :
  (Prims.bool * FStarC_Interactive_Ide_Types.repl_state)=
  let st1 =
    FStarC_Interactive_PushHelper.push_repl "run_repl_transaction" push_kind
      task st in
  let uu___ =
    FStarC_Interactive_PushHelper.track_name_changes
      st1.FStarC_Interactive_Ide_Types.repl_env in
  match uu___ with
  | (env, finish_name_tracking) ->
      let check_success uu___1 =
        (let uu___2 = FStarC_Errors.get_err_count () in
         uu___2 = Prims.int_zero) && (Prims.op_Negation must_rollback) in
      let uu___1 =
        let uu___2 =
          with_captured_errors env FStarC_Util.sigint_raise
            (fun env1 ->
               let uu___3 =
                 FStarC_Interactive_PushHelper.run_repl_task
                   st1.FStarC_Interactive_Ide_Types.repl_fname
                   st1.FStarC_Interactive_Ide_Types.repl_curmod env1 task
                   st1.FStarC_Interactive_Ide_Types.repl_lang in
               FStar_Pervasives_Native.Some uu___3) in
        match uu___2 with
        | FStar_Pervasives_Native.Some (curmod, env1, lds) when
            check_success () -> (curmod, env1, true, lds)
        | uu___3 ->
            ((st1.FStarC_Interactive_Ide_Types.repl_curmod), env, false, []) in
      (match uu___1 with
       | (curmod, env1, success, lds) ->
           let uu___2 = finish_name_tracking env1 in
           (match uu___2 with
            | (env2, name_events) ->
                let st2 =
                  if success
                  then
                    let st3 =
                      {
                        FStarC_Interactive_Ide_Types.repl_line =
                          (st1.FStarC_Interactive_Ide_Types.repl_line);
                        FStarC_Interactive_Ide_Types.repl_column =
                          (st1.FStarC_Interactive_Ide_Types.repl_column);
                        FStarC_Interactive_Ide_Types.repl_fname =
                          (st1.FStarC_Interactive_Ide_Types.repl_fname);
                        FStarC_Interactive_Ide_Types.repl_deps_stack =
                          (st1.FStarC_Interactive_Ide_Types.repl_deps_stack);
                        FStarC_Interactive_Ide_Types.repl_curmod = curmod;
                        FStarC_Interactive_Ide_Types.repl_env = env2;
                        FStarC_Interactive_Ide_Types.repl_stdin =
                          (st1.FStarC_Interactive_Ide_Types.repl_stdin);
                        FStarC_Interactive_Ide_Types.repl_names =
                          (st1.FStarC_Interactive_Ide_Types.repl_names);
                        FStarC_Interactive_Ide_Types.repl_buffered_input_queries
                          =
                          (st1.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
                        FStarC_Interactive_Ide_Types.repl_lang =
                          (FStarC_List.op_At (FStarC_List.rev lds)
                             st1.FStarC_Interactive_Ide_Types.repl_lang)
                      } in
                    FStarC_Interactive_PushHelper.commit_name_tracking st3
                      name_events
                  else
                    FStarC_Interactive_PushHelper.pop_repl
                      "run_repl_transaction" st1 in
                (success, st2)))
let run_repl_ld_transactions (st : FStarC_Interactive_Ide_Types.repl_state)
  (tasks : FStarC_Interactive_Ide_Types.repl_task Prims.list)
  (progress_callback : FStarC_Interactive_Ide_Types.repl_task -> unit) :
  (FStarC_Interactive_Ide_Types.repl_state,
    FStarC_Interactive_Ide_Types.repl_state) FStar_Pervasives.either=
  let debug verb task =
    let uu___ = FStarC_Effect.op_Bang dbg in
    if uu___
    then
      let uu___1 = FStarC_Interactive_Ide_Types.string_of_repl_task task in
      FStarC_Format.print2 "%s %s" verb uu___1
    else () in
  let rec revert_many st1 uu___ =
    match uu___ with
    | [] -> st1
    | (_id, (task, _st'))::entries ->
        (debug "Reverting" task;
         (let st' =
            FStarC_Interactive_PushHelper.pop_repl "run_repl_ls_transactions"
              st1 in
          let dep_graph =
            FStarC_TypeChecker_Env.dep_graph
              st1.FStarC_Interactive_Ide_Types.repl_env in
          let st'1 =
            let uu___3 =
              FStarC_TypeChecker_Env.set_dep_graph
                st'.FStarC_Interactive_Ide_Types.repl_env dep_graph in
            {
              FStarC_Interactive_Ide_Types.repl_line =
                (st'.FStarC_Interactive_Ide_Types.repl_line);
              FStarC_Interactive_Ide_Types.repl_column =
                (st'.FStarC_Interactive_Ide_Types.repl_column);
              FStarC_Interactive_Ide_Types.repl_fname =
                (st'.FStarC_Interactive_Ide_Types.repl_fname);
              FStarC_Interactive_Ide_Types.repl_deps_stack =
                (st'.FStarC_Interactive_Ide_Types.repl_deps_stack);
              FStarC_Interactive_Ide_Types.repl_curmod =
                (st'.FStarC_Interactive_Ide_Types.repl_curmod);
              FStarC_Interactive_Ide_Types.repl_env = uu___3;
              FStarC_Interactive_Ide_Types.repl_stdin =
                (st'.FStarC_Interactive_Ide_Types.repl_stdin);
              FStarC_Interactive_Ide_Types.repl_names =
                (st'.FStarC_Interactive_Ide_Types.repl_names);
              FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
                (st'.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
              FStarC_Interactive_Ide_Types.repl_lang =
                (st'.FStarC_Interactive_Ide_Types.repl_lang)
            } in
          revert_many st'1 entries)) in
  let rec aux st1 tasks1 previous =
    match (tasks1, previous) with
    | ([], []) -> FStar_Pervasives.Inl st1
    | (task::tasks2, []) ->
        (debug "Loading" task;
         progress_callback task;
         (let uu___3 = FStarC_Options.restore_cmd_line_options false in ());
         (let timestamped_task =
            FStarC_Interactive_PushHelper.update_task_timestamps task in
          let push_kind =
            let uu___3 = FStarC_Options.lax () in
            if uu___3
            then FStarC_Interactive_Ide_Types.LaxCheck
            else FStarC_Interactive_Ide_Types.FullCheck in
          let uu___3 =
            run_repl_transaction st1 (FStar_Pervasives_Native.Some push_kind)
              false timestamped_task in
          match uu___3 with
          | (success, st2) ->
              if success
              then
                let uu___4 =
                  let uu___5 =
                    FStarC_Effect.op_Bang
                      FStarC_Interactive_PushHelper.repl_stack in
                  {
                    FStarC_Interactive_Ide_Types.repl_line =
                      (st2.FStarC_Interactive_Ide_Types.repl_line);
                    FStarC_Interactive_Ide_Types.repl_column =
                      (st2.FStarC_Interactive_Ide_Types.repl_column);
                    FStarC_Interactive_Ide_Types.repl_fname =
                      (st2.FStarC_Interactive_Ide_Types.repl_fname);
                    FStarC_Interactive_Ide_Types.repl_deps_stack = uu___5;
                    FStarC_Interactive_Ide_Types.repl_curmod =
                      (st2.FStarC_Interactive_Ide_Types.repl_curmod);
                    FStarC_Interactive_Ide_Types.repl_env =
                      (st2.FStarC_Interactive_Ide_Types.repl_env);
                    FStarC_Interactive_Ide_Types.repl_stdin =
                      (st2.FStarC_Interactive_Ide_Types.repl_stdin);
                    FStarC_Interactive_Ide_Types.repl_names =
                      (st2.FStarC_Interactive_Ide_Types.repl_names);
                    FStarC_Interactive_Ide_Types.repl_buffered_input_queries
                      =
                      (st2.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
                    FStarC_Interactive_Ide_Types.repl_lang =
                      (st2.FStarC_Interactive_Ide_Types.repl_lang)
                  } in
                aux uu___4 tasks2 []
              else FStar_Pervasives.Inr st2))
    | (task::tasks2, prev::previous1) when
        let uu___ = FStarC_Interactive_PushHelper.update_task_timestamps task in
        (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev)) =
          uu___
        -> (debug "Skipping" task; aux st1 tasks2 previous1)
    | (tasks2, previous1) ->
        let uu___ = revert_many st1 previous1 in aux uu___ tasks2 [] in
  aux st tasks
    (FStarC_List.rev st.FStarC_Interactive_Ide_Types.repl_deps_stack)
let wrap_js_failure (qid : Prims.string) (expected : Prims.string)
  (got : FStarC_Json.json) : FStarC_Interactive_Ide_Types.query=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Interactive_JsonHelper.json_debug got in
      FStarC_Format.fmt2 "JSON decoding failed: expected %s, got %s" expected
        uu___2 in
    FStarC_Interactive_Ide_Types.ProtocolViolation uu___1 in
  {
    FStarC_Interactive_Ide_Types.qq = uu___;
    FStarC_Interactive_Ide_Types.qid = qid
  }
let unpack_interactive_query (st : FStarC_Interactive_Ide_Types.repl_state)
  (json : FStarC_Json.json) : FStarC_Interactive_Ide_Types.query=
  let assoc errloc key a =
    let uu___ = FStarC_Interactive_JsonHelper.try_assoc key a in
    match uu___ with
    | FStar_Pervasives_Native.Some v -> v
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 =
            FStarC_Format.fmt2 "Missing key [%s] in %s." key errloc in
          FStarC_Interactive_JsonHelper.InvalidQuery uu___2 in
        FStarC_Effect.raise uu___1 in
  let request = FStarC_Interactive_JsonHelper.js_assoc json in
  let qid =
    let uu___ = assoc "query" "query-id" request in
    FStarC_Interactive_JsonHelper.js_str uu___ in
  try
    (fun uu___ ->
       match () with
       | () ->
           let query =
             let uu___1 = assoc "query" "query" request in
             FStarC_Interactive_JsonHelper.js_str uu___1 in
           let args =
             let uu___1 = assoc "query" "args" request in
             FStarC_Interactive_JsonHelper.js_assoc uu___1 in
           let arg k = assoc "[args]" k args in
           let try_arg k =
             let uu___1 = FStarC_Interactive_JsonHelper.try_assoc k args in
             match uu___1 with
             | FStar_Pervasives_Native.Some (FStarC_Json.JsonNull) ->
                 FStar_Pervasives_Native.None
             | other -> other in
           let read_position err loc =
             let uu___1 =
               let uu___2 = assoc err "filename" loc in
               FStarC_Interactive_JsonHelper.js_str uu___2 in
             let uu___2 =
               let uu___3 = assoc err "line" loc in
               FStarC_Interactive_JsonHelper.js_int uu___3 in
             let uu___3 =
               let uu___4 = assoc err "column" loc in
               FStarC_Interactive_JsonHelper.js_int uu___4 in
             (uu___1, uu___2, uu___3) in
           let read_to_position uu___1 =
             let to_pos =
               let uu___2 = arg "to-position" in
               FStarC_Interactive_JsonHelper.js_assoc uu___2 in
             let uu___2 =
               let uu___3 = assoc "to-position.line" "line" to_pos in
               FStarC_Interactive_JsonHelper.js_int uu___3 in
             let uu___3 =
               let uu___4 = assoc "to-position.column" "column" to_pos in
               FStarC_Interactive_JsonHelper.js_int uu___4 in
             ((st.FStarC_Interactive_Ide_Types.repl_fname), uu___2, uu___3) in
           let parse_full_buffer_kind kind =
             match kind with
             | "full" -> FStarC_Interactive_Ide_Types.Full
             | "lax" -> FStarC_Interactive_Ide_Types.Lax
             | "cache" -> FStarC_Interactive_Ide_Types.Cache
             | "reload-deps" -> FStarC_Interactive_Ide_Types.ReloadDeps
             | "verify-to-position" ->
                 let uu___1 = read_to_position () in
                 FStarC_Interactive_Ide_Types.VerifyToPosition uu___1
             | "lax-to-position" ->
                 let uu___1 = read_to_position () in
                 FStarC_Interactive_Ide_Types.LaxToPosition uu___1
             | uu___1 ->
                 FStarC_Effect.raise
                   (FStarC_Interactive_JsonHelper.InvalidQuery
                      "Invalid full-buffer kind") in
           let uu___1 =
             match query with
             | "exit" -> FStarC_Interactive_Ide_Types.Exit
             | "pop" -> FStarC_Interactive_Ide_Types.Pop
             | "describe-protocol" ->
                 FStarC_Interactive_Ide_Types.DescribeProtocol
             | "describe-repl" -> FStarC_Interactive_Ide_Types.DescribeRepl
             | "segment" ->
                 let uu___2 =
                   let uu___3 = arg "code" in
                   FStarC_Interactive_JsonHelper.js_str uu___3 in
                 FStarC_Interactive_Ide_Types.Segment uu___2
             | "peek" ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = arg "kind" in
                     FStarC_Interactive_Ide_Types.js_pushkind uu___4 in
                   let uu___4 =
                     let uu___5 = arg "line" in
                     FStarC_Interactive_JsonHelper.js_int uu___5 in
                   let uu___5 =
                     let uu___6 = arg "column" in
                     FStarC_Interactive_JsonHelper.js_int uu___6 in
                   let uu___6 =
                     let uu___7 =
                       let uu___8 = arg "code" in
                       FStarC_Interactive_JsonHelper.js_str uu___8 in
                     FStar_Pervasives.Inl uu___7 in
                   {
                     FStarC_Interactive_Ide_Types.push_kind = uu___3;
                     FStarC_Interactive_Ide_Types.push_line = uu___4;
                     FStarC_Interactive_Ide_Types.push_column = uu___5;
                     FStarC_Interactive_Ide_Types.push_peek_only =
                       (query = "peek");
                     FStarC_Interactive_Ide_Types.push_code_or_decl = uu___6
                   } in
                 FStarC_Interactive_Ide_Types.Push uu___2
             | "push" ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = arg "kind" in
                     FStarC_Interactive_Ide_Types.js_pushkind uu___4 in
                   let uu___4 =
                     let uu___5 = arg "line" in
                     FStarC_Interactive_JsonHelper.js_int uu___5 in
                   let uu___5 =
                     let uu___6 = arg "column" in
                     FStarC_Interactive_JsonHelper.js_int uu___6 in
                   let uu___6 =
                     let uu___7 =
                       let uu___8 = arg "code" in
                       FStarC_Interactive_JsonHelper.js_str uu___8 in
                     FStar_Pervasives.Inl uu___7 in
                   {
                     FStarC_Interactive_Ide_Types.push_kind = uu___3;
                     FStarC_Interactive_Ide_Types.push_line = uu___4;
                     FStarC_Interactive_Ide_Types.push_column = uu___5;
                     FStarC_Interactive_Ide_Types.push_peek_only =
                       (query = "peek");
                     FStarC_Interactive_Ide_Types.push_code_or_decl = uu___6
                   } in
                 FStarC_Interactive_Ide_Types.Push uu___2
             | "push-partial-checked-file" ->
                 let uu___2 =
                   let uu___3 = arg "until-lid" in
                   FStarC_Interactive_JsonHelper.js_str uu___3 in
                 FStarC_Interactive_Ide_Types.PushPartialCheckedFile uu___2
             | "full-buffer" ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = arg "code" in
                     FStarC_Interactive_JsonHelper.js_str uu___4 in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = arg "kind" in
                       FStarC_Interactive_JsonHelper.js_str uu___6 in
                     parse_full_buffer_kind uu___5 in
                   let uu___5 =
                     let uu___6 = arg "with-symbols" in
                     FStarC_Interactive_JsonHelper.js_bool uu___6 in
                   (uu___3, uu___4, uu___5) in
                 FStarC_Interactive_Ide_Types.FullBuffer uu___2
             | "autocomplete" ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = arg "partial-symbol" in
                     FStarC_Interactive_JsonHelper.js_str uu___4 in
                   let uu___4 =
                     let uu___5 = try_arg "context" in
                     FStarC_Interactive_Ide_Types.js_optional_completion_context
                       uu___5 in
                   (uu___3, uu___4) in
                 FStarC_Interactive_Ide_Types.AutoComplete uu___2
             | "lookup" ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = arg "symbol" in
                     FStarC_Interactive_JsonHelper.js_str uu___4 in
                   let uu___4 =
                     let uu___5 = try_arg "context" in
                     FStarC_Interactive_Ide_Types.js_optional_lookup_context
                       uu___5 in
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = try_arg "location" in
                       FStarC_Option.map
                         FStarC_Interactive_JsonHelper.js_assoc uu___7 in
                     FStarC_Option.map (read_position "[location]") uu___6 in
                   let uu___6 =
                     let uu___7 = arg "requested-info" in
                     FStarC_Interactive_JsonHelper.js_list
                       FStarC_Interactive_JsonHelper.js_str uu___7 in
                   let uu___7 = try_arg "symbol-range" in
                   (uu___3, uu___4, uu___5, uu___6, uu___7) in
                 FStarC_Interactive_Ide_Types.Lookup uu___2
             | "compute" ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = arg "term" in
                     FStarC_Interactive_JsonHelper.js_str uu___4 in
                   let uu___4 =
                     let uu___5 = try_arg "rules" in
                     FStarC_Option.map
                       (FStarC_Interactive_JsonHelper.js_list
                          FStarC_Interactive_Ide_Types.js_reductionrule)
                       uu___5 in
                   (uu___3, uu___4) in
                 FStarC_Interactive_Ide_Types.Compute uu___2
             | "search" ->
                 let uu___2 =
                   let uu___3 = arg "terms" in
                   FStarC_Interactive_JsonHelper.js_str uu___3 in
                 FStarC_Interactive_Ide_Types.Search uu___2
             | "vfs-add" ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = try_arg "filename" in
                     FStarC_Option.map FStarC_Interactive_JsonHelper.js_str
                       uu___4 in
                   let uu___4 =
                     let uu___5 = arg "contents" in
                     FStarC_Interactive_JsonHelper.js_str uu___5 in
                   (uu___3, uu___4) in
                 FStarC_Interactive_Ide_Types.VfsAdd uu___2
             | "format" ->
                 let uu___2 =
                   let uu___3 = arg "code" in
                   FStarC_Interactive_JsonHelper.js_str uu___3 in
                 FStarC_Interactive_Ide_Types.Format uu___2
             | "restart-solver" -> FStarC_Interactive_Ide_Types.RestartSolver
             | "cancel" ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = arg "cancel-line" in
                       FStarC_Interactive_JsonHelper.js_int uu___5 in
                     let uu___5 =
                       let uu___6 = arg "cancel-column" in
                       FStarC_Interactive_JsonHelper.js_int uu___6 in
                     ((st.FStarC_Interactive_Ide_Types.repl_fname), uu___4,
                       uu___5) in
                   FStar_Pervasives_Native.Some uu___3 in
                 FStarC_Interactive_Ide_Types.Cancel uu___2
             | uu___2 ->
                 let uu___3 = FStarC_Format.fmt1 "Unknown query '%s'" query in
                 FStarC_Interactive_Ide_Types.ProtocolViolation uu___3 in
           {
             FStarC_Interactive_Ide_Types.qq = uu___1;
             FStarC_Interactive_Ide_Types.qid = qid
           }) ()
  with
  | FStarC_Interactive_JsonHelper.InvalidQuery msg ->
      {
        FStarC_Interactive_Ide_Types.qq =
          (FStarC_Interactive_Ide_Types.ProtocolViolation msg);
        FStarC_Interactive_Ide_Types.qid = qid
      }
  | FStarC_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
      wrap_js_failure qid expected got
let deserialize_interactive_query
  (st : FStarC_Interactive_Ide_Types.repl_state)
  (js_query : FStarC_Json.json) : FStarC_Interactive_Ide_Types.query=
  try
    (fun uu___ -> match () with | () -> unpack_interactive_query st js_query)
      ()
  with
  | FStarC_Interactive_JsonHelper.InvalidQuery msg ->
      {
        FStarC_Interactive_Ide_Types.qq =
          (FStarC_Interactive_Ide_Types.ProtocolViolation msg);
        FStarC_Interactive_Ide_Types.qid = "?"
      }
  | FStarC_Interactive_JsonHelper.UnexpectedJsonType (expected, got) ->
      wrap_js_failure "?" expected got
let parse_interactive_query (st : FStarC_Interactive_Ide_Types.repl_state)
  (query_str : Prims.string) : FStarC_Interactive_Ide_Types.query=
  let uu___ = FStarC_Json.json_of_string query_str in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      {
        FStarC_Interactive_Ide_Types.qq =
          (FStarC_Interactive_Ide_Types.ProtocolViolation
             "Json parsing failed.");
        FStarC_Interactive_Ide_Types.qid = "?"
      }
  | FStar_Pervasives_Native.Some request ->
      deserialize_interactive_query st request
let buffer_input_queries (st : FStarC_Interactive_Ide_Types.repl_state) :
  FStarC_Interactive_Ide_Types.repl_state=
  let rec aux qs st1 =
    let done1 qs1 st2 =
      {
        FStarC_Interactive_Ide_Types.repl_line =
          (st2.FStarC_Interactive_Ide_Types.repl_line);
        FStarC_Interactive_Ide_Types.repl_column =
          (st2.FStarC_Interactive_Ide_Types.repl_column);
        FStarC_Interactive_Ide_Types.repl_fname =
          (st2.FStarC_Interactive_Ide_Types.repl_fname);
        FStarC_Interactive_Ide_Types.repl_deps_stack =
          (st2.FStarC_Interactive_Ide_Types.repl_deps_stack);
        FStarC_Interactive_Ide_Types.repl_curmod =
          (st2.FStarC_Interactive_Ide_Types.repl_curmod);
        FStarC_Interactive_Ide_Types.repl_env =
          (st2.FStarC_Interactive_Ide_Types.repl_env);
        FStarC_Interactive_Ide_Types.repl_stdin =
          (st2.FStarC_Interactive_Ide_Types.repl_stdin);
        FStarC_Interactive_Ide_Types.repl_names =
          (st2.FStarC_Interactive_Ide_Types.repl_names);
        FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
          (FStarC_List.op_At
             st2.FStarC_Interactive_Ide_Types.repl_buffered_input_queries
             (FStarC_List.rev qs1));
        FStarC_Interactive_Ide_Types.repl_lang =
          (st2.FStarC_Interactive_Ide_Types.repl_lang)
      } in
    let uu___ =
      let uu___1 = FStarC_Util.poll_stdin (FStarC_Util.float_of_string "0.0") in
      Prims.op_Negation uu___1 in
    if uu___
    then done1 qs st1
    else
      (let uu___2 =
         FStarC_Util.read_line st1.FStarC_Interactive_Ide_Types.repl_stdin in
       match uu___2 with
       | FStar_Pervasives_Native.None -> done1 qs st1
       | FStar_Pervasives_Native.Some line ->
           let q = parse_interactive_query st1 line in
           (match q.FStarC_Interactive_Ide_Types.qq with
            | FStarC_Interactive_Ide_Types.Cancel uu___3 ->
                {
                  FStarC_Interactive_Ide_Types.repl_line =
                    (st1.FStarC_Interactive_Ide_Types.repl_line);
                  FStarC_Interactive_Ide_Types.repl_column =
                    (st1.FStarC_Interactive_Ide_Types.repl_column);
                  FStarC_Interactive_Ide_Types.repl_fname =
                    (st1.FStarC_Interactive_Ide_Types.repl_fname);
                  FStarC_Interactive_Ide_Types.repl_deps_stack =
                    (st1.FStarC_Interactive_Ide_Types.repl_deps_stack);
                  FStarC_Interactive_Ide_Types.repl_curmod =
                    (st1.FStarC_Interactive_Ide_Types.repl_curmod);
                  FStarC_Interactive_Ide_Types.repl_env =
                    (st1.FStarC_Interactive_Ide_Types.repl_env);
                  FStarC_Interactive_Ide_Types.repl_stdin =
                    (st1.FStarC_Interactive_Ide_Types.repl_stdin);
                  FStarC_Interactive_Ide_Types.repl_names =
                    (st1.FStarC_Interactive_Ide_Types.repl_names);
                  FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
                    [q];
                  FStarC_Interactive_Ide_Types.repl_lang =
                    (st1.FStarC_Interactive_Ide_Types.repl_lang)
                }
            | uu___3 -> aux (q :: qs) st1)) in
  aux [] st
let read_interactive_query (st : FStarC_Interactive_Ide_Types.repl_state) :
  (FStarC_Interactive_Ide_Types.query *
    FStarC_Interactive_Ide_Types.repl_state) FStar_Pervasives_Native.option=
  match st.FStarC_Interactive_Ide_Types.repl_buffered_input_queries with
  | [] ->
      let uu___ =
        FStarC_Util.read_line st.FStarC_Interactive_Ide_Types.repl_stdin in
      (match uu___ with
       | FStar_Pervasives_Native.None ->
           (FStarC_Util.kill_all (); FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.Some line ->
           let uu___1 =
             let uu___2 = parse_interactive_query st line in (uu___2, st) in
           FStar_Pervasives_Native.Some uu___1)
  | q::qs ->
      FStar_Pervasives_Native.Some
        (q,
          {
            FStarC_Interactive_Ide_Types.repl_line =
              (st.FStarC_Interactive_Ide_Types.repl_line);
            FStarC_Interactive_Ide_Types.repl_column =
              (st.FStarC_Interactive_Ide_Types.repl_column);
            FStarC_Interactive_Ide_Types.repl_fname =
              (st.FStarC_Interactive_Ide_Types.repl_fname);
            FStarC_Interactive_Ide_Types.repl_deps_stack =
              (st.FStarC_Interactive_Ide_Types.repl_deps_stack);
            FStarC_Interactive_Ide_Types.repl_curmod =
              (st.FStarC_Interactive_Ide_Types.repl_curmod);
            FStarC_Interactive_Ide_Types.repl_env =
              (st.FStarC_Interactive_Ide_Types.repl_env);
            FStarC_Interactive_Ide_Types.repl_stdin =
              (st.FStarC_Interactive_Ide_Types.repl_stdin);
            FStarC_Interactive_Ide_Types.repl_names =
              (st.FStarC_Interactive_Ide_Types.repl_names);
            FStarC_Interactive_Ide_Types.repl_buffered_input_queries = qs;
            FStarC_Interactive_Ide_Types.repl_lang =
              (st.FStarC_Interactive_Ide_Types.repl_lang)
          })
let json_of_opt (json_of_a : 'uuuuu -> FStarC_Json.json)
  (opt_a : 'uuuuu FStar_Pervasives_Native.option) : FStarC_Json.json=
  let uu___ = FStarC_Option.map json_of_a opt_a in
  FStarC_Option.dflt FStarC_Json.JsonNull uu___
let alist_of_symbol_lookup_result
  (lr : FStarC_Interactive_QueryHelper.sl_reponse) (symbol : Prims.string)
  (symrange_opt : FStarC_Json.json FStar_Pervasives_Native.option) :
  (Prims.string * FStarC_Json.json) Prims.list=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          json_of_opt
            (fun r ->
               let uu___4 = FStarC_Range_Ops.refind_range r in
               FStarC_Range_Ops.json_of_def_range uu___4)
            lr.FStarC_Interactive_QueryHelper.slr_def_range in
        ("defined-at", uu___3) in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            json_of_opt (fun uu___6 -> FStarC_Json.JsonStr uu___6)
              lr.FStarC_Interactive_QueryHelper.slr_typ in
          ("type", uu___5) in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              json_of_opt (fun uu___8 -> FStarC_Json.JsonStr uu___8)
                lr.FStarC_Interactive_QueryHelper.slr_doc in
            ("documentation", uu___7) in
          let uu___7 =
            let uu___8 =
              let uu___9 =
                json_of_opt (fun uu___10 -> FStarC_Json.JsonStr uu___10)
                  lr.FStarC_Interactive_QueryHelper.slr_def in
              ("definition", uu___9) in
            [uu___8] in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    ("name",
      (FStarC_Json.JsonStr (lr.FStarC_Interactive_QueryHelper.slr_name))) ::
      uu___1 in
  let uu___1 =
    match symrange_opt with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some symrange ->
        let uu___2 =
          let uu___3 = json_of_opt (fun x -> x) symrange_opt in
          ("symbol-range", uu___3) in
        [uu___2; ("symbol", (FStarC_Json.JsonStr symbol))] in
  FStarC_List.op_At uu___ uu___1
let alist_of_protocol_info : (Prims.string * FStarC_Json.json) Prims.list=
  let js_version =
    FStarC_Json.JsonInt
      FStarC_Interactive_Ide_Types.interactive_protocol_vernum in
  let js_features =
    let uu___ =
      FStarC_List.map (fun uu___1 -> FStarC_Json.JsonStr uu___1)
        FStarC_Interactive_Ide_Types.interactive_protocol_features in
    FStarC_Json.JsonList uu___ in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet 
  | OptReadOnly 
let uu___is_OptSet (projectee : fstar_option_permission_level) : Prims.bool=
  match projectee with | OptSet -> true | uu___ -> false
let uu___is_OptReadOnly (projectee : fstar_option_permission_level) :
  Prims.bool= match projectee with | OptReadOnly -> true | uu___ -> false
let string_of_option_permission_level (uu___ : fstar_option_permission_level)
  : Prims.string=
  match uu___ with | OptSet -> "" | OptReadOnly -> "read-only"
type fstar_option =
  {
  opt_name: Prims.string ;
  opt_sig: Prims.string ;
  opt_value: FStarC_Options.option_val ;
  opt_default: FStarC_Options.option_val ;
  opt_type: FStarC_Options.opt_type ;
  opt_snippets: Prims.string Prims.list ;
  opt_documentation: Prims.string FStar_Pervasives_Native.option ;
  opt_permission_level: fstar_option_permission_level }
let __proj__Mkfstar_option__item__opt_name (projectee : fstar_option) :
  Prims.string=
  match projectee with
  | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
      opt_documentation; opt_permission_level;_} -> opt_name
let __proj__Mkfstar_option__item__opt_sig (projectee : fstar_option) :
  Prims.string=
  match projectee with
  | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
      opt_documentation; opt_permission_level;_} -> opt_sig
let __proj__Mkfstar_option__item__opt_value (projectee : fstar_option) :
  FStarC_Options.option_val=
  match projectee with
  | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
      opt_documentation; opt_permission_level;_} -> opt_value
let __proj__Mkfstar_option__item__opt_default (projectee : fstar_option) :
  FStarC_Options.option_val=
  match projectee with
  | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
      opt_documentation; opt_permission_level;_} -> opt_default
let __proj__Mkfstar_option__item__opt_type (projectee : fstar_option) :
  FStarC_Options.opt_type=
  match projectee with
  | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
      opt_documentation; opt_permission_level;_} -> opt_type
let __proj__Mkfstar_option__item__opt_snippets (projectee : fstar_option) :
  Prims.string Prims.list=
  match projectee with
  | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
      opt_documentation; opt_permission_level;_} -> opt_snippets
let __proj__Mkfstar_option__item__opt_documentation
  (projectee : fstar_option) : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
      opt_documentation; opt_permission_level;_} -> opt_documentation
let __proj__Mkfstar_option__item__opt_permission_level
  (projectee : fstar_option) : fstar_option_permission_level=
  match projectee with
  | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
      opt_documentation; opt_permission_level;_} -> opt_permission_level
let rec kind_of_fstar_option_type (uu___ : FStarC_Options.opt_type) :
  Prims.string=
  match uu___ with
  | FStarC_Options.Const uu___1 -> "flag"
  | FStarC_Options.IntStr uu___1 -> "int"
  | FStarC_Options.BoolStr -> "bool"
  | FStarC_Options.PathStr uu___1 -> "path"
  | FStarC_Options.SimpleStr uu___1 -> "string"
  | FStarC_Options.EnumStr uu___1 -> "enum"
  | FStarC_Options.OpenEnumStr uu___1 -> "open enum"
  | FStarC_Options.PostProcessed (uu___1, typ) ->
      kind_of_fstar_option_type typ
  | FStarC_Options.Accumulated typ -> kind_of_fstar_option_type typ
  | FStarC_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
  | FStarC_Options.WithSideEffect (uu___1, typ) ->
      kind_of_fstar_option_type typ
let snippets_of_fstar_option (name : Prims.string)
  (typ : FStarC_Options.opt_type) : Prims.string Prims.list=
  let mk_field field_name = Prims.strcat "${" (Prims.strcat field_name "}") in
  let mk_snippet name1 argstring =
    Prims.strcat "--"
      (Prims.strcat name1
         (if argstring <> "" then Prims.strcat " " argstring else "")) in
  let rec arg_snippets_of_type typ1 =
    match typ1 with
    | FStarC_Options.Const uu___ -> [""]
    | FStarC_Options.BoolStr -> ["true"; "false"]
    | FStarC_Options.IntStr desc -> [mk_field desc]
    | FStarC_Options.PathStr desc -> [mk_field desc]
    | FStarC_Options.SimpleStr desc -> [mk_field desc]
    | FStarC_Options.EnumStr strs -> strs
    | FStarC_Options.OpenEnumStr (strs, desc) ->
        FStarC_List.op_At strs [mk_field desc]
    | FStarC_Options.PostProcessed (uu___, elem_spec) ->
        arg_snippets_of_type elem_spec
    | FStarC_Options.Accumulated elem_spec -> arg_snippets_of_type elem_spec
    | FStarC_Options.ReverseAccumulated elem_spec ->
        arg_snippets_of_type elem_spec
    | FStarC_Options.WithSideEffect (uu___, elem_spec) ->
        arg_snippets_of_type elem_spec in
  let uu___ = arg_snippets_of_type typ in
  FStarC_List.map (mk_snippet name) uu___
let rec json_of_fstar_option_value (uu___ : FStarC_Options.option_val) :
  FStarC_Json.json=
  match uu___ with
  | FStarC_Options.Bool b -> FStarC_Json.JsonBool b
  | FStarC_Options.String s -> FStarC_Json.JsonStr s
  | FStarC_Options.Path s -> FStarC_Json.JsonStr s
  | FStarC_Options.Int n -> FStarC_Json.JsonInt n
  | FStarC_Options.List vs ->
      let uu___1 = FStarC_List.map json_of_fstar_option_value vs in
      FStarC_Json.JsonList uu___1
  | FStarC_Options.Unset -> FStarC_Json.JsonNull
let alist_of_fstar_option (opt : fstar_option) :
  (Prims.string * FStarC_Json.json) Prims.list=
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
              json_of_opt (fun uu___8 -> FStarC_Json.JsonStr uu___8)
                opt.opt_documentation in
            ("documentation", uu___7) in
          let uu___7 =
            let uu___8 =
              let uu___9 =
                let uu___10 = kind_of_fstar_option_type opt.opt_type in
                FStarC_Json.JsonStr uu___10 in
              ("type", uu___9) in
            [uu___8;
            ("permission-level",
              (FStarC_Json.JsonStr
                 (string_of_option_permission_level opt.opt_permission_level)))] in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    ("signature", (FStarC_Json.JsonStr (opt.opt_sig))) :: uu___1 in
  ("name", (FStarC_Json.JsonStr (opt.opt_name))) :: uu___
let json_of_fstar_option (opt : fstar_option) : FStarC_Json.json=
  let uu___ = alist_of_fstar_option opt in FStarC_Json.JsonAssoc uu___
let json_of_response (qid : Prims.string)
  (status : FStarC_Interactive_Ide_Types.query_status)
  (response : FStarC_Json.json) : FStarC_Json.json=
  let qid1 = FStarC_Json.JsonStr qid in
  let status1 =
    match status with
    | FStarC_Interactive_Ide_Types.QueryOK -> FStarC_Json.JsonStr "success"
    | FStarC_Interactive_Ide_Types.QueryNOK -> FStarC_Json.JsonStr "failure"
    | FStarC_Interactive_Ide_Types.QueryViolatesProtocol ->
        FStarC_Json.JsonStr "protocol-violation" in
  FStarC_Json.JsonAssoc
    [("kind", (FStarC_Json.JsonStr "response"));
    ("query-id", qid1);
    ("status", status1);
    ("response", response)]
let write_response (qid : Prims.string)
  (status : FStarC_Interactive_Ide_Types.query_status)
  (response : FStarC_Json.json) : unit=
  FStarC_Interactive_JsonHelper.write_json
    (json_of_response qid status response)
let json_of_message (level : Prims.string) (js_contents : FStarC_Json.json) :
  FStarC_Json.json=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang repl_current_qid in
          json_of_opt (fun uu___5 -> FStarC_Json.JsonStr uu___5) uu___4 in
        ("query-id", uu___3) in
      [uu___2;
      ("level", (FStarC_Json.JsonStr level));
      ("contents", js_contents)] in
    ("kind", (FStarC_Json.JsonStr "message")) :: uu___1 in
  FStarC_Json.JsonAssoc uu___
let forward_message (callback : FStarC_Json.json -> 'uuuuu)
  (level : Prims.string) (contents : FStarC_Json.json) : 'uuuuu=
  let uu___ = json_of_message level contents in callback uu___
let json_of_hello : FStarC_Json.json=
  let js_version =
    FStarC_Json.JsonInt
      FStarC_Interactive_Ide_Types.interactive_protocol_vernum in
  let js_features =
    let uu___ =
      FStarC_List.map (fun uu___1 -> FStarC_Json.JsonStr uu___1)
        FStarC_Interactive_Ide_Types.interactive_protocol_features in
    FStarC_Json.JsonList uu___ in
  FStarC_Json.JsonAssoc (("kind", (FStarC_Json.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
let write_hello (uu___ : unit) : unit=
  FStarC_Interactive_JsonHelper.write_json json_of_hello
let sig_of_fstar_option (name : Prims.string) (typ : FStarC_Options.opt_type)
  : Prims.string=
  let flag = Prims.strcat "--" name in
  let uu___ = FStarC_Options.desc_of_opt_type typ in
  match uu___ with
  | FStar_Pervasives_Native.None -> flag
  | FStar_Pervasives_Native.Some arg_sig ->
      Prims.strcat flag (Prims.strcat " " arg_sig)
let fstar_options_list_cache : fstar_option Prims.list=
  let defaults = FStarC_SMap.of_list FStarC_Options.defaults in
  let uu___ =
    FStarC_List.filter_map
      (fun uu___1 ->
         match uu___1 with
         | (_shortname, name, typ, doc) ->
             let uu___2 = FStarC_SMap.try_find defaults name in
             FStarC_Option.map
               (fun default_value ->
                  let uu___3 = sig_of_fstar_option name typ in
                  let uu___4 = snippets_of_fstar_option name typ in
                  let uu___5 =
                    if doc = FStar_Pprint.empty
                    then FStar_Pervasives_Native.None
                    else
                      (let uu___7 = FStarC_Errors_Msg.renderdoc doc in
                       FStar_Pervasives_Native.Some uu___7) in
                  let uu___6 =
                    let uu___7 = FStarC_Options.settable name in
                    if uu___7 then OptSet else OptReadOnly in
                  {
                    opt_name = name;
                    opt_sig = uu___3;
                    opt_value = FStarC_Options.Unset;
                    opt_default = default_value;
                    opt_type = typ;
                    opt_snippets = uu___4;
                    opt_documentation = uu___5;
                    opt_permission_level = uu___6
                  }) uu___2) FStarC_Options.all_specs_with_types in
  FStarC_List.sortWith
    (fun o1 o2 ->
       FStarC_String.compare (FStarC_String.lowercase o1.opt_name)
         (FStarC_String.lowercase o2.opt_name)) uu___
let fstar_options_map_cache : fstar_option FStarC_SMap.t=
  let cache = FStarC_SMap.create (Prims.of_int (50)) in
  FStarC_List.iter (fun opt -> FStarC_SMap.add cache opt.opt_name opt)
    fstar_options_list_cache;
  cache
let update_option (opt : fstar_option) : fstar_option=
  let uu___ = FStarC_Options.get_option opt.opt_name in
  {
    opt_name = (opt.opt_name);
    opt_sig = (opt.opt_sig);
    opt_value = uu___;
    opt_default = (opt.opt_default);
    opt_type = (opt.opt_type);
    opt_snippets = (opt.opt_snippets);
    opt_documentation = (opt.opt_documentation);
    opt_permission_level = (opt.opt_permission_level)
  }
let current_fstar_options (filter : fstar_option -> Prims.bool) :
  fstar_option Prims.list=
  let uu___ = FStarC_List.filter filter fstar_options_list_cache in
  FStarC_List.map update_option uu___
let trim_option_name (opt_name : Prims.string) :
  (Prims.string * Prims.string)=
  let opt_prefix = "--" in
  if FStarC_Util.starts_with opt_name opt_prefix
  then
    let uu___ =
      FStarC_Util.substring_from opt_name (FStarC_String.length opt_prefix) in
    (opt_prefix, uu___)
  else ("", opt_name)
let json_of_repl_state (st : FStarC_Interactive_Ide_Types.repl_state) :
  FStarC_Json.json=
  let filenames uu___ =
    match uu___ with
    | (uu___1, (task, uu___2)) ->
        (match task with
         | FStarC_Interactive_Ide_Types.LDInterleaved (intf, impl) ->
             [intf.FStarC_Interactive_Ide_Types.tf_fname;
             impl.FStarC_Interactive_Ide_Types.tf_fname]
         | FStarC_Interactive_Ide_Types.LDSingle intf_or_impl ->
             [intf_or_impl.FStarC_Interactive_Ide_Types.tf_fname]
         | FStarC_Interactive_Ide_Types.LDInterfaceOfCurrentFile intf ->
             [intf.FStarC_Interactive_Ide_Types.tf_fname]
         | uu___3 -> []) in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_List.concatMap filenames
              st.FStarC_Interactive_Ide_Types.repl_deps_stack in
          FStarC_List.map (fun uu___5 -> FStarC_Json.JsonStr uu___5) uu___4 in
        FStarC_Json.JsonList uu___3 in
      ("loaded-dependencies", uu___2) in
    let uu___2 =
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 = current_fstar_options (fun uu___7 -> true) in
            FStarC_List.map json_of_fstar_option uu___6 in
          FStarC_Json.JsonList uu___5 in
        ("options", uu___4) in
      [uu___3] in
    uu___1 :: uu___2 in
  FStarC_Json.JsonAssoc uu___
let run_exit (st : 'uuuuu) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) * (
    'uuuuu1, Prims.int) FStar_Pervasives.either)=
  ((FStarC_Interactive_Ide_Types.QueryOK, FStarC_Json.JsonNull),
    (FStar_Pervasives.Inr Prims.int_zero))
let run_describe_protocol (st : 'uuuuu) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) * (
    'uuuuu, 'uuuuu1) FStar_Pervasives.either)=
  ((FStarC_Interactive_Ide_Types.QueryOK,
     (FStarC_Json.JsonAssoc alist_of_protocol_info)),
    (FStar_Pervasives.Inl st))
let run_describe_repl (st : FStarC_Interactive_Ide_Types.repl_state) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  let uu___ =
    let uu___1 = json_of_repl_state st in
    (FStarC_Interactive_Ide_Types.QueryOK, uu___1) in
  (uu___, (FStar_Pervasives.Inl st))
let run_protocol_violation (st : 'uuuuu) (message : Prims.string) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) * (
    'uuuuu, 'uuuuu1) FStar_Pervasives.either)=
  ((FStarC_Interactive_Ide_Types.QueryViolatesProtocol,
     (FStarC_Json.JsonStr message)), (FStar_Pervasives.Inl st))
let run_generic_error (st : 'uuuuu) (message : Prims.string) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) * (
    'uuuuu, 'uuuuu1) FStar_Pervasives.either)=
  ((FStarC_Interactive_Ide_Types.QueryNOK, (FStarC_Json.JsonStr message)),
    (FStar_Pervasives.Inl st))
let collect_errors (uu___ : unit) : FStarC_Errors.issue Prims.list=
  let errors = FStarC_Errors.report_all () in FStarC_Errors.clear (); errors
let run_segment (st : FStarC_Interactive_Ide_Types.repl_state)
  (code : Prims.string) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  let frag =
    {
      FStarC_Parser_ParseIt.frag_fname =
        (st.FStarC_Interactive_Ide_Types.repl_fname);
      FStarC_Parser_ParseIt.frag_text = code;
      FStarC_Parser_ParseIt.frag_line = Prims.int_one;
      FStarC_Parser_ParseIt.frag_col = Prims.int_zero
    } in
  let collect_decls uu___ =
    let uu___1 =
      FStarC_Parser_Driver.parse_fragment FStar_Pervasives_Native.None frag in
    match uu___1 with
    | FStarC_Parser_Driver.Empty -> []
    | FStarC_Parser_Driver.Decls decls -> decls
    | FStarC_Parser_Driver.Modul (FStarC_Parser_AST.Module
        { FStarC_Parser_AST.no_prelude = uu___2;
          FStarC_Parser_AST.mname = uu___3;
          FStarC_Parser_AST.decls = decls;_})
        -> decls
    | FStarC_Parser_Driver.Modul (FStarC_Parser_AST.Interface
        { FStarC_Parser_AST.no_prelude1 = uu___2;
          FStarC_Parser_AST.mname1 = uu___3;
          FStarC_Parser_AST.decls1 = decls;
          FStarC_Parser_AST.admitted = uu___4;_})
        -> decls in
  let uu___ =
    with_captured_errors st.FStarC_Interactive_Ide_Types.repl_env
      FStarC_Util.sigint_ignore
      (fun uu___1 ->
         let uu___2 = collect_decls () in FStar_Pervasives_Native.Some uu___2) in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let errors =
        let uu___1 = collect_errors () in
        FStarC_List.map json_of_issue uu___1 in
      ((FStarC_Interactive_Ide_Types.QueryNOK, (FStarC_Json.JsonList errors)),
        (FStar_Pervasives.Inl st))
  | FStar_Pervasives_Native.Some decls ->
      let json_of_decl decl =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Range_Ops.json_of_def_range
                decl.FStarC_Parser_AST.drange in
            ("def_range", uu___3) in
          [uu___2] in
        FStarC_Json.JsonAssoc uu___1 in
      let js_decls =
        let uu___1 = FStarC_List.map json_of_decl decls in
        FStarC_Json.JsonList uu___1 in
      ((FStarC_Interactive_Ide_Types.QueryOK,
         (FStarC_Json.JsonAssoc [("decls", js_decls)])),
        (FStar_Pervasives.Inl st))
let run_vfs_add (st : FStarC_Interactive_Ide_Types.repl_state)
  (opt_fname : Prims.string FStar_Pervasives_Native.option)
  (contents : Prims.string) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  let fname =
    FStarC_Option.dflt st.FStarC_Interactive_Ide_Types.repl_fname opt_fname in
  FStarC_Parser_ParseIt.add_vfs_entry fname contents;
  ((FStarC_Interactive_Ide_Types.QueryOK, FStarC_Json.JsonNull),
    (FStar_Pervasives.Inl st))
let run_pop (st : FStarC_Interactive_Ide_Types.repl_state) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  let uu___ = nothing_left_to_pop st in
  if uu___
  then
    ((FStarC_Interactive_Ide_Types.QueryNOK,
       (FStarC_Json.JsonStr "Too many pops")), (FStar_Pervasives.Inl st))
  else
    (let st' = FStarC_Interactive_PushHelper.pop_repl "pop_query" st in
     ((FStarC_Interactive_Ide_Types.QueryOK, FStarC_Json.JsonNull),
       (FStar_Pervasives.Inl st')))
let write_progress (stage : Prims.string FStar_Pervasives_Native.option)
  (contents_alist : (Prims.string * FStarC_Json.json) Prims.list) : unit=
  let stage1 =
    match stage with
    | FStar_Pervasives_Native.Some s -> FStarC_Json.JsonStr s
    | FStar_Pervasives_Native.None -> FStarC_Json.JsonNull in
  let js_contents = ("stage", stage1) :: contents_alist in
  let uu___ = json_of_message "progress" (FStarC_Json.JsonAssoc js_contents) in
  FStarC_Interactive_JsonHelper.write_json uu___
let write_error (contents : (Prims.string * FStarC_Json.json) Prims.list) :
  unit=
  let uu___ = json_of_message "error" (FStarC_Json.JsonAssoc contents) in
  FStarC_Interactive_JsonHelper.write_json uu___
let write_repl_ld_task_progress
  (task : FStarC_Interactive_Ide_Types.repl_task) : unit=
  match task with
  | FStarC_Interactive_Ide_Types.LDInterleaved (uu___, tf) ->
      let modname =
        FStarC_Parser_Dep.module_name_of_file
          tf.FStarC_Interactive_Ide_Types.tf_fname in
      write_progress (FStar_Pervasives_Native.Some "loading-dependency")
        [("modname", (FStarC_Json.JsonStr modname))]
  | FStarC_Interactive_Ide_Types.LDSingle tf ->
      let modname =
        FStarC_Parser_Dep.module_name_of_file
          tf.FStarC_Interactive_Ide_Types.tf_fname in
      write_progress (FStar_Pervasives_Native.Some "loading-dependency")
        [("modname", (FStarC_Json.JsonStr modname))]
  | FStarC_Interactive_Ide_Types.LDInterfaceOfCurrentFile tf ->
      let modname =
        FStarC_Parser_Dep.module_name_of_file
          tf.FStarC_Interactive_Ide_Types.tf_fname in
      write_progress (FStar_Pervasives_Native.Some "loading-dependency")
        [("modname", (FStarC_Json.JsonStr modname))]
  | uu___ -> ()
let load_deps (st : FStarC_Interactive_Ide_Types.repl_state) :
  ((FStarC_Interactive_Ide_Types.repl_state * Prims.string Prims.list),
    FStarC_Interactive_Ide_Types.repl_state) FStar_Pervasives.either=
  let uu___ =
    with_captured_errors st.FStarC_Interactive_Ide_Types.repl_env
      FStarC_Util.sigint_ignore
      (fun _env ->
         let uu___1 =
           FStarC_Interactive_PushHelper.deps_and_repl_ld_tasks_of_our_file
             st.FStarC_Interactive_Ide_Types.repl_fname in
         FStar_Pervasives_Native.Some uu___1) in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives.Inr st
  | FStar_Pervasives_Native.Some (deps, tasks, dep_graph) ->
      let st1 =
        let uu___1 =
          FStarC_TypeChecker_Env.set_dep_graph
            st.FStarC_Interactive_Ide_Types.repl_env dep_graph in
        {
          FStarC_Interactive_Ide_Types.repl_line =
            (st.FStarC_Interactive_Ide_Types.repl_line);
          FStarC_Interactive_Ide_Types.repl_column =
            (st.FStarC_Interactive_Ide_Types.repl_column);
          FStarC_Interactive_Ide_Types.repl_fname =
            (st.FStarC_Interactive_Ide_Types.repl_fname);
          FStarC_Interactive_Ide_Types.repl_deps_stack =
            (st.FStarC_Interactive_Ide_Types.repl_deps_stack);
          FStarC_Interactive_Ide_Types.repl_curmod =
            (st.FStarC_Interactive_Ide_Types.repl_curmod);
          FStarC_Interactive_Ide_Types.repl_env = uu___1;
          FStarC_Interactive_Ide_Types.repl_stdin =
            (st.FStarC_Interactive_Ide_Types.repl_stdin);
          FStarC_Interactive_Ide_Types.repl_names =
            (st.FStarC_Interactive_Ide_Types.repl_names);
          FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
            (st.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
          FStarC_Interactive_Ide_Types.repl_lang =
            (st.FStarC_Interactive_Ide_Types.repl_lang)
        } in
      let uu___1 =
        run_repl_ld_transactions st1 tasks write_repl_ld_task_progress in
      (match uu___1 with
       | FStar_Pervasives.Inr st2 ->
           (write_progress FStar_Pervasives_Native.None [];
            FStar_Pervasives.Inr st2)
       | FStar_Pervasives.Inl st2 ->
           (write_progress FStar_Pervasives_Native.None [];
            FStar_Pervasives.Inl (st2, deps)))
let rephrase_dependency_error (issue : FStarC_Errors.issue) :
  FStarC_Errors.issue=
  let uu___ =
    let uu___1 =
      FStarC_Errors_Msg.text "Error while computing or loading dependencies" in
    uu___1 :: (issue.FStarC_Errors.issue_msg) in
  {
    FStarC_Errors.issue_msg = uu___;
    FStarC_Errors.issue_level = (issue.FStarC_Errors.issue_level);
    FStarC_Errors.issue_range = (issue.FStarC_Errors.issue_range);
    FStarC_Errors.issue_number = (issue.FStarC_Errors.issue_number);
    FStarC_Errors.issue_ctx = (issue.FStarC_Errors.issue_ctx)
  }
let write_full_buffer_fragment_progress
  (di : FStarC_Interactive_Incremental.fragment_progress) : unit=
  let json_of_code_fragment cf =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Range_Ops.json_of_def_range cf.FStarC_Parser_ParseIt.range in
        ("range", uu___2) in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              FStarC_Util.digest_of_string cf.FStarC_Parser_ParseIt.code in
            FStarC_Json.JsonStr uu___5 in
          ("code-digest", uu___4) in
        [uu___3] in
      uu___1 :: uu___2 in
    FStarC_Json.JsonAssoc uu___ in
  match di with
  | FStarC_Interactive_Incremental.FullBufferStarted ->
      write_progress (FStar_Pervasives_Native.Some "full-buffer-started") []
  | FStarC_Interactive_Incremental.FragmentStarted d ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Range_Ops.json_of_def_range d.FStarC_Parser_AST.drange in
          ("ranges", uu___2) in
        [uu___1] in
      write_progress
        (FStar_Pervasives_Native.Some "full-buffer-fragment-started") uu___
  | FStarC_Interactive_Incremental.FragmentSuccess
      (d, cf, FStarC_Interactive_Ide_Types.FullCheck) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Range_Ops.json_of_def_range d.FStarC_Parser_AST.drange in
          ("ranges", uu___2) in
        let uu___2 =
          let uu___3 =
            let uu___4 = json_of_code_fragment cf in
            ("code-fragment", uu___4) in
          [uu___3] in
        uu___1 :: uu___2 in
      write_progress (FStar_Pervasives_Native.Some "full-buffer-fragment-ok")
        uu___
  | FStarC_Interactive_Incremental.FragmentSuccess
      (d, cf, FStarC_Interactive_Ide_Types.LaxCheck) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Range_Ops.json_of_def_range d.FStarC_Parser_AST.drange in
          ("ranges", uu___2) in
        let uu___2 =
          let uu___3 =
            let uu___4 = json_of_code_fragment cf in
            ("code-fragment", uu___4) in
          [uu___3] in
        uu___1 :: uu___2 in
      write_progress
        (FStar_Pervasives_Native.Some "full-buffer-fragment-lax-ok") uu___
  | FStarC_Interactive_Incremental.FragmentFailed d ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Range_Ops.json_of_def_range d.FStarC_Parser_AST.drange in
          ("ranges", uu___2) in
        [uu___1] in
      write_progress
        (FStar_Pervasives_Native.Some "full-buffer-fragment-failed") uu___
  | FStarC_Interactive_Incremental.FragmentError issues ->
      let qid =
        let uu___ = FStarC_Effect.op_Bang repl_current_qid in
        match uu___ with
        | FStar_Pervasives_Native.None -> "unknown"
        | FStar_Pervasives_Native.Some q -> q in
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map json_of_issue issues in
          FStarC_Json.JsonList uu___2 in
        json_of_response qid FStarC_Interactive_Ide_Types.QueryNOK uu___1 in
      FStarC_Interactive_JsonHelper.write_json uu___
  | FStarC_Interactive_Incremental.FullBufferFinished ->
      write_progress (FStar_Pervasives_Native.Some "full-buffer-finished") []
let trunc_modul (m : FStarC_Syntax_Syntax.modul)
  (pred : FStarC_Syntax_Syntax.sigelt -> Prims.bool) :
  (Prims.bool * FStarC_Syntax_Syntax.modul)=
  let rec filter decls acc =
    match decls with
    | [] -> (false, (FStarC_List.rev acc))
    | d::ds ->
        let uu___ = pred d in
        if uu___ then (true, (FStarC_List.rev acc)) else filter ds (d :: acc) in
  let uu___ = filter m.FStarC_Syntax_Syntax.declarations [] in
  match uu___ with
  | (found, decls) ->
      (found,
        {
          FStarC_Syntax_Syntax.name = (m.FStarC_Syntax_Syntax.name);
          FStarC_Syntax_Syntax.declarations = decls;
          FStarC_Syntax_Syntax.is_interface =
            (m.FStarC_Syntax_Syntax.is_interface)
        })
let load_partial_checked_file (env : FStarC_TypeChecker_Env.env)
  (filename : Prims.string) (until_lid : Prims.string) :
  (FStarC_TypeChecker_Env.env * FStarC_Syntax_Syntax.modul)=
  let uu___ = FStarC_CheckedFiles.load_module_from_cache env filename in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      failwith (Prims.strcat "cannot find checked file for " filename)
  | FStar_Pervasives_Native.Some tc_result ->
      let uu___1 =
        FStarC_Universal.with_dsenv_of_tcenv env
          (fun ds ->
             let uu___2 =
               FStarC_Syntax_DsEnv.set_current_module ds
                 (tc_result.FStarC_CheckedFiles.checked_module).FStarC_Syntax_Syntax.name in
             ((), uu___2)) in
      (match uu___1 with
       | (uu___2, env1) ->
           let uu___3 =
             FStarC_Universal.with_dsenv_of_tcenv env1
               (fun ds ->
                  let uu___4 =
                    FStarC_Syntax_DsEnv.set_iface_decls ds
                      (tc_result.FStarC_CheckedFiles.checked_module).FStarC_Syntax_Syntax.name
                      [] in
                  ((), uu___4)) in
           (match uu___3 with
            | (uu___4, env2) ->
                let pred se =
                  let rec pred1 lids =
                    match lids with
                    | [] -> false
                    | lid::lids1 ->
                        let uu___5 =
                          let uu___6 = FStarC_Ident.string_of_lid lid in
                          uu___6 = until_lid in
                        if uu___5 then true else pred1 lids1 in
                  let uu___5 = FStarC_Syntax_Util.lids_of_sigelt se in
                  pred1 uu___5 in
                let uu___5 =
                  trunc_modul tc_result.FStarC_CheckedFiles.checked_module
                    pred in
                (match uu___5 with
                 | (found_decl, m) ->
                     if Prims.op_Negation found_decl
                     then
                       failwith
                         (Prims.strcat
                            "did not find declaration with lident " until_lid)
                     else
                       (let uu___7 =
                          let uu___8 =
                            FStarC_ToSyntax_ToSyntax.add_partial_modul_to_env
                              m tc_result.FStarC_CheckedFiles.mii
                              (FStarC_TypeChecker_Normalize.erase_universes
                                 env2) in
                          FStarC_Universal.with_dsenv_of_tcenv env2 uu___8 in
                        match uu___7 with
                        | (uu___8, env3) ->
                            let env4 =
                              FStarC_TypeChecker_Tc.load_partial_checked_module
                                env3 m in
                            let uu___9 =
                              FStarC_Universal.with_dsenv_of_tcenv env4
                                (fun ds ->
                                   let uu___10 =
                                     FStarC_Syntax_DsEnv.set_current_module
                                       ds m.FStarC_Syntax_Syntax.name in
                                   ((), uu___10)) in
                            (match uu___9 with
                             | (uu___10, env5) ->
                                 let env6 =
                                   FStarC_TypeChecker_Env.set_current_module
                                     env5 m.FStarC_Syntax_Syntax.name in
                                 ((let uu___12 =
                                     FStarC_SMTEncoding_Encode.encode_modul
                                       env6 m in
                                   ());
                                  (env6, m)))))))
let run_load_partial_file (st : FStarC_Interactive_Ide_Types.repl_state)
  (decl_name : Prims.string) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, Prims.int)
    FStar_Pervasives.either)=
  let uu___ = load_deps st in
  match uu___ with
  | FStar_Pervasives.Inr st1 ->
      let errors =
        let uu___1 = collect_errors () in
        FStarC_List.map rephrase_dependency_error uu___1 in
      let js_errors = FStarC_List.map json_of_issue errors in
      ((FStarC_Interactive_Ide_Types.QueryNOK,
         (FStarC_Json.JsonList js_errors)), (FStar_Pervasives.Inl st1))
  | FStar_Pervasives.Inl (st1, deps) ->
      let st2 =
        FStarC_Interactive_PushHelper.push_repl "load partial file"
          (FStar_Pervasives_Native.Some
             FStarC_Interactive_Ide_Types.FullCheck)
          FStarC_Interactive_Ide_Types.Noop st1 in
      let env = st2.FStarC_Interactive_Ide_Types.repl_env in
      let uu___1 =
        with_captured_errors env FStarC_Util.sigint_raise
          (fun env1 ->
             let uu___2 =
               load_partial_checked_file env1
                 st2.FStarC_Interactive_Ide_Types.repl_fname decl_name in
             FStar_Pervasives_Native.Some uu___2) in
      (match uu___1 with
       | FStar_Pervasives_Native.Some (env1, curmod) when
           let uu___2 = FStarC_Errors.get_err_count () in
           uu___2 = Prims.int_zero ->
           let st3 =
             {
               FStarC_Interactive_Ide_Types.repl_line =
                 (st2.FStarC_Interactive_Ide_Types.repl_line);
               FStarC_Interactive_Ide_Types.repl_column =
                 (st2.FStarC_Interactive_Ide_Types.repl_column);
               FStarC_Interactive_Ide_Types.repl_fname =
                 (st2.FStarC_Interactive_Ide_Types.repl_fname);
               FStarC_Interactive_Ide_Types.repl_deps_stack =
                 (st2.FStarC_Interactive_Ide_Types.repl_deps_stack);
               FStarC_Interactive_Ide_Types.repl_curmod =
                 (FStar_Pervasives_Native.Some curmod);
               FStarC_Interactive_Ide_Types.repl_env = env1;
               FStarC_Interactive_Ide_Types.repl_stdin =
                 (st2.FStarC_Interactive_Ide_Types.repl_stdin);
               FStarC_Interactive_Ide_Types.repl_names =
                 (st2.FStarC_Interactive_Ide_Types.repl_names);
               FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
                 (st2.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
               FStarC_Interactive_Ide_Types.repl_lang =
                 (st2.FStarC_Interactive_Ide_Types.repl_lang)
             } in
           ((FStarC_Interactive_Ide_Types.QueryOK, (FStarC_Json.JsonList [])),
             (FStar_Pervasives.Inl st3))
       | uu___2 ->
           let json_error_list =
             let uu___3 = collect_errors () in
             FStarC_List.map json_of_issue uu___3 in
           let json_errors = FStarC_Json.JsonList json_error_list in
           let st3 =
             FStarC_Interactive_PushHelper.pop_repl "load partial file" st2 in
           ((FStarC_Interactive_Ide_Types.QueryNOK, json_errors),
             (FStar_Pervasives.Inl st3)))
let json_errors (uu___ : unit) : FStarC_Json.json Prims.list=
  let errors =
    let uu___1 = collect_errors () in
    FStarC_List.map rephrase_dependency_error uu___1 in
  let js_errors = FStarC_List.map json_of_issue errors in js_errors
let run_push_without_deps (st : FStarC_Interactive_Ide_Types.repl_state)
  (query : FStarC_Interactive_Ide_Types.push_query) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, Prims.int)
    FStar_Pervasives.either)=
  let set_flychecking_flag st1 flag =
    {
      FStarC_Interactive_Ide_Types.repl_line =
        (st1.FStarC_Interactive_Ide_Types.repl_line);
      FStarC_Interactive_Ide_Types.repl_column =
        (st1.FStarC_Interactive_Ide_Types.repl_column);
      FStarC_Interactive_Ide_Types.repl_fname =
        (st1.FStarC_Interactive_Ide_Types.repl_fname);
      FStarC_Interactive_Ide_Types.repl_deps_stack =
        (st1.FStarC_Interactive_Ide_Types.repl_deps_stack);
      FStarC_Interactive_Ide_Types.repl_curmod =
        (st1.FStarC_Interactive_Ide_Types.repl_curmod);
      FStarC_Interactive_Ide_Types.repl_env =
        (let uu___ = st1.FStarC_Interactive_Ide_Types.repl_env in
         {
           FStarC_TypeChecker_Env.solver =
             (uu___.FStarC_TypeChecker_Env.solver);
           FStarC_TypeChecker_Env.range =
             (uu___.FStarC_TypeChecker_Env.range);
           FStarC_TypeChecker_Env.curmodule =
             (uu___.FStarC_TypeChecker_Env.curmodule);
           FStarC_TypeChecker_Env.gamma =
             (uu___.FStarC_TypeChecker_Env.gamma);
           FStarC_TypeChecker_Env.gamma_sig =
             (uu___.FStarC_TypeChecker_Env.gamma_sig);
           FStarC_TypeChecker_Env.gamma_cache =
             (uu___.FStarC_TypeChecker_Env.gamma_cache);
           FStarC_TypeChecker_Env.modules =
             (uu___.FStarC_TypeChecker_Env.modules);
           FStarC_TypeChecker_Env.expected_typ =
             (uu___.FStarC_TypeChecker_Env.expected_typ);
           FStarC_TypeChecker_Env.sigtab =
             (uu___.FStarC_TypeChecker_Env.sigtab);
           FStarC_TypeChecker_Env.attrtab =
             (uu___.FStarC_TypeChecker_Env.attrtab);
           FStarC_TypeChecker_Env.instantiate_imp =
             (uu___.FStarC_TypeChecker_Env.instantiate_imp);
           FStarC_TypeChecker_Env.effects =
             (uu___.FStarC_TypeChecker_Env.effects);
           FStarC_TypeChecker_Env.generalize =
             (uu___.FStarC_TypeChecker_Env.generalize);
           FStarC_TypeChecker_Env.letrecs =
             (uu___.FStarC_TypeChecker_Env.letrecs);
           FStarC_TypeChecker_Env.top_level =
             (uu___.FStarC_TypeChecker_Env.top_level);
           FStarC_TypeChecker_Env.check_uvars =
             (uu___.FStarC_TypeChecker_Env.check_uvars);
           FStarC_TypeChecker_Env.use_eq_strict =
             (uu___.FStarC_TypeChecker_Env.use_eq_strict);
           FStarC_TypeChecker_Env.is_iface =
             (uu___.FStarC_TypeChecker_Env.is_iface);
           FStarC_TypeChecker_Env.admit =
             (uu___.FStarC_TypeChecker_Env.admit);
           FStarC_TypeChecker_Env.phase1 =
             (uu___.FStarC_TypeChecker_Env.phase1);
           FStarC_TypeChecker_Env.failhard =
             (uu___.FStarC_TypeChecker_Env.failhard);
           FStarC_TypeChecker_Env.flychecking = flag;
           FStarC_TypeChecker_Env.uvar_subtyping =
             (uu___.FStarC_TypeChecker_Env.uvar_subtyping);
           FStarC_TypeChecker_Env.intactics =
             (uu___.FStarC_TypeChecker_Env.intactics);
           FStarC_TypeChecker_Env.nocoerce =
             (uu___.FStarC_TypeChecker_Env.nocoerce);
           FStarC_TypeChecker_Env.tc_term =
             (uu___.FStarC_TypeChecker_Env.tc_term);
           FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
             (uu___.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
           FStarC_TypeChecker_Env.universe_of =
             (uu___.FStarC_TypeChecker_Env.universe_of);
           FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
             (uu___.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
           FStarC_TypeChecker_Env.teq_nosmt_force =
             (uu___.FStarC_TypeChecker_Env.teq_nosmt_force);
           FStarC_TypeChecker_Env.subtype_nosmt_force =
             (uu___.FStarC_TypeChecker_Env.subtype_nosmt_force);
           FStarC_TypeChecker_Env.qtbl_name_and_index =
             (uu___.FStarC_TypeChecker_Env.qtbl_name_and_index);
           FStarC_TypeChecker_Env.normalized_eff_names =
             (uu___.FStarC_TypeChecker_Env.normalized_eff_names);
           FStarC_TypeChecker_Env.fv_delta_depths =
             (uu___.FStarC_TypeChecker_Env.fv_delta_depths);
           FStarC_TypeChecker_Env.proof_ns =
             (uu___.FStarC_TypeChecker_Env.proof_ns);
           FStarC_TypeChecker_Env.synth_hook =
             (uu___.FStarC_TypeChecker_Env.synth_hook);
           FStarC_TypeChecker_Env.try_solve_implicits_hook =
             (uu___.FStarC_TypeChecker_Env.try_solve_implicits_hook);
           FStarC_TypeChecker_Env.splice =
             (uu___.FStarC_TypeChecker_Env.splice);
           FStarC_TypeChecker_Env.mpreprocess =
             (uu___.FStarC_TypeChecker_Env.mpreprocess);
           FStarC_TypeChecker_Env.postprocess =
             (uu___.FStarC_TypeChecker_Env.postprocess);
           FStarC_TypeChecker_Env.identifier_info =
             (uu___.FStarC_TypeChecker_Env.identifier_info);
           FStarC_TypeChecker_Env.tc_hooks =
             (uu___.FStarC_TypeChecker_Env.tc_hooks);
           FStarC_TypeChecker_Env.dsenv =
             (uu___.FStarC_TypeChecker_Env.dsenv);
           FStarC_TypeChecker_Env.nbe = (uu___.FStarC_TypeChecker_Env.nbe);
           FStarC_TypeChecker_Env.strict_args_tab =
             (uu___.FStarC_TypeChecker_Env.strict_args_tab);
           FStarC_TypeChecker_Env.erasable_types_tab =
             (uu___.FStarC_TypeChecker_Env.erasable_types_tab);
           FStarC_TypeChecker_Env.enable_defer_to_tac =
             (uu___.FStarC_TypeChecker_Env.enable_defer_to_tac);
           FStarC_TypeChecker_Env.unif_allow_ref_guards =
             (uu___.FStarC_TypeChecker_Env.unif_allow_ref_guards);
           FStarC_TypeChecker_Env.erase_erasable_args =
             (uu___.FStarC_TypeChecker_Env.erase_erasable_args);
           FStarC_TypeChecker_Env.core_check =
             (uu___.FStarC_TypeChecker_Env.core_check);
           FStarC_TypeChecker_Env.missing_decl =
             (uu___.FStarC_TypeChecker_Env.missing_decl)
         });
      FStarC_Interactive_Ide_Types.repl_stdin =
        (st1.FStarC_Interactive_Ide_Types.repl_stdin);
      FStarC_Interactive_Ide_Types.repl_names =
        (st1.FStarC_Interactive_Ide_Types.repl_names);
      FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
        (st1.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
      FStarC_Interactive_Ide_Types.repl_lang =
        (st1.FStarC_Interactive_Ide_Types.repl_lang)
    } in
  let uu___ = query in
  match uu___ with
  | { FStarC_Interactive_Ide_Types.push_kind = push_kind;
      FStarC_Interactive_Ide_Types.push_line = line;
      FStarC_Interactive_Ide_Types.push_column = column;
      FStarC_Interactive_Ide_Types.push_peek_only = peek_only;
      FStarC_Interactive_Ide_Types.push_code_or_decl = code_or_decl;_} ->
      ((let uu___2 = FStarC_Options.ide_id_info_off () in
        if uu___2
        then
          FStarC_TypeChecker_Env.toggle_id_info
            st.FStarC_Interactive_Ide_Types.repl_env false
        else
          FStarC_TypeChecker_Env.toggle_id_info
            st.FStarC_Interactive_Ide_Types.repl_env true);
       (let frag =
          match code_or_decl with
          | FStar_Pervasives.Inl text ->
              FStar_Pervasives.Inl
                {
                  FStarC_Parser_ParseIt.frag_fname =
                    (st.FStarC_Interactive_Ide_Types.repl_fname);
                  FStarC_Parser_ParseIt.frag_text = text;
                  FStarC_Parser_ParseIt.frag_line = line;
                  FStarC_Parser_ParseIt.frag_col = column
                }
          | FStar_Pervasives.Inr (decl, _code) -> FStar_Pervasives.Inr decl in
        let st1 = set_flychecking_flag st peek_only in
        let uu___2 =
          run_repl_transaction st1 (FStar_Pervasives_Native.Some push_kind)
            peek_only
            (FStarC_Interactive_Ide_Types.PushFragment
               (frag, push_kind, [], [])) in
        match uu___2 with
        | (success, st2) ->
            let st3 = set_flychecking_flag st2 false in
            let status =
              if success || peek_only
              then FStarC_Interactive_Ide_Types.QueryOK
              else FStarC_Interactive_Ide_Types.QueryNOK in
            let errs = collect_errors () in
            let has_error =
              FStarC_List.existsb
                (fun i ->
                   match i.FStarC_Errors.issue_level with
                   | FStarC_Errors.EError -> true
                   | FStarC_Errors.ENotImplemented -> true
                   | uu___3 -> false) errs in
            ((match code_or_decl with
              | FStar_Pervasives.Inr (d, s) ->
                  if Prims.op_Negation has_error
                  then
                    write_full_buffer_fragment_progress
                      (FStarC_Interactive_Incremental.FragmentSuccess
                         (d, s, push_kind))
                  else
                    write_full_buffer_fragment_progress
                      (FStarC_Interactive_Incremental.FragmentFailed d)
              | uu___4 -> ());
             (let json_errors1 =
                let uu___4 = FStarC_List.map json_of_issue errs in
                FStarC_Json.JsonList uu___4 in
              (match (errs, status) with
               | (uu___5::uu___6, FStarC_Interactive_Ide_Types.QueryOK) ->
                   FStarC_Interactive_PushHelper.add_issues_to_push_fragment
                     [json_errors1]
               | uu___5 -> ());
              (let st4 =
                 if success
                 then
                   {
                     FStarC_Interactive_Ide_Types.repl_line = line;
                     FStarC_Interactive_Ide_Types.repl_column = column;
                     FStarC_Interactive_Ide_Types.repl_fname =
                       (st3.FStarC_Interactive_Ide_Types.repl_fname);
                     FStarC_Interactive_Ide_Types.repl_deps_stack =
                       (st3.FStarC_Interactive_Ide_Types.repl_deps_stack);
                     FStarC_Interactive_Ide_Types.repl_curmod =
                       (st3.FStarC_Interactive_Ide_Types.repl_curmod);
                     FStarC_Interactive_Ide_Types.repl_env =
                       (st3.FStarC_Interactive_Ide_Types.repl_env);
                     FStarC_Interactive_Ide_Types.repl_stdin =
                       (st3.FStarC_Interactive_Ide_Types.repl_stdin);
                     FStarC_Interactive_Ide_Types.repl_names =
                       (st3.FStarC_Interactive_Ide_Types.repl_names);
                     FStarC_Interactive_Ide_Types.repl_buffered_input_queries
                       =
                       (st3.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
                     FStarC_Interactive_Ide_Types.repl_lang =
                       (st3.FStarC_Interactive_Ide_Types.repl_lang)
                   }
                 else st3 in
               ((status, json_errors1), (FStar_Pervasives.Inl st4)))))))
let run_push_with_deps (st : FStarC_Interactive_Ide_Types.repl_state)
  (query : FStarC_Interactive_Ide_Types.push_query) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, Prims.int)
    FStar_Pervasives.either)=
  (let uu___1 = FStarC_Effect.op_Bang dbg in
   if uu___1 then FStarC_Format.print_string "Reloading dependencies" else ());
  FStarC_TypeChecker_Env.toggle_id_info
    st.FStarC_Interactive_Ide_Types.repl_env false;
  (let uu___2 = load_deps st in
   match uu___2 with
   | FStar_Pervasives.Inr st1 ->
       let errors =
         let uu___3 = collect_errors () in
         FStarC_List.map rephrase_dependency_error uu___3 in
       let js_errors = FStarC_List.map json_of_issue errors in
       ((FStarC_Interactive_Ide_Types.QueryNOK,
          (FStarC_Json.JsonList js_errors)), (FStar_Pervasives.Inl st1))
   | FStar_Pervasives.Inl (st1, deps) ->
       ((let uu___4 = FStarC_Options.restore_cmd_line_options false in ());
        (let names =
           FStarC_Interactive_PushHelper.add_module_completions
             st1.FStarC_Interactive_Ide_Types.repl_fname deps
             st1.FStarC_Interactive_Ide_Types.repl_names in
         run_push_without_deps
           {
             FStarC_Interactive_Ide_Types.repl_line =
               (st1.FStarC_Interactive_Ide_Types.repl_line);
             FStarC_Interactive_Ide_Types.repl_column =
               (st1.FStarC_Interactive_Ide_Types.repl_column);
             FStarC_Interactive_Ide_Types.repl_fname =
               (st1.FStarC_Interactive_Ide_Types.repl_fname);
             FStarC_Interactive_Ide_Types.repl_deps_stack =
               (st1.FStarC_Interactive_Ide_Types.repl_deps_stack);
             FStarC_Interactive_Ide_Types.repl_curmod =
               (st1.FStarC_Interactive_Ide_Types.repl_curmod);
             FStarC_Interactive_Ide_Types.repl_env =
               (st1.FStarC_Interactive_Ide_Types.repl_env);
             FStarC_Interactive_Ide_Types.repl_stdin =
               (st1.FStarC_Interactive_Ide_Types.repl_stdin);
             FStarC_Interactive_Ide_Types.repl_names = names;
             FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
               (st1.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
             FStarC_Interactive_Ide_Types.repl_lang =
               (st1.FStarC_Interactive_Ide_Types.repl_lang)
           } query)))
let run_push (st : FStarC_Interactive_Ide_Types.repl_state)
  (query : FStarC_Interactive_Ide_Types.push_query) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, Prims.int)
    FStar_Pervasives.either)=
  let uu___ =
    (let uu___1 = FStarC_Parser_Dep.fly_deps_enabled () in
     Prims.op_Negation uu___1) && (nothing_left_to_pop st) in
  if uu___
  then run_push_with_deps st query
  else run_push_without_deps st query
let run_symbol_lookup (st : FStarC_Interactive_Ide_Types.repl_state)
  (symbol : Prims.string)
  (pos_opt :
    FStarC_Interactive_QueryHelper.position FStar_Pervasives_Native.option)
  (requested_info : Prims.string Prims.list)
  (symbol_range_opt : FStarC_Json.json FStar_Pervasives_Native.option) :
  (Prims.string,
    (Prims.string * (Prims.string * FStarC_Json.json) Prims.list))
    FStar_Pervasives.either=
  let uu___ =
    FStarC_Interactive_QueryHelper.symlookup
      st.FStarC_Interactive_Ide_Types.repl_env symbol pos_opt requested_info in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives.Inl "Symbol not found"
  | FStar_Pervasives_Native.Some result ->
      let uu___1 =
        let uu___2 =
          alist_of_symbol_lookup_result result symbol symbol_range_opt in
        ("symbol", uu___2) in
      FStar_Pervasives.Inr uu___1
let run_option_lookup (opt_name : Prims.string) :
  (Prims.string,
    (Prims.string * (Prims.string * FStarC_Json.json) Prims.list))
    FStar_Pervasives.either=
  let uu___ = trim_option_name opt_name in
  match uu___ with
  | (uu___1, trimmed_name) ->
      let uu___2 = FStarC_SMap.try_find fstar_options_map_cache trimmed_name in
      (match uu___2 with
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives.Inl (Prims.strcat "Unknown option:" opt_name)
       | FStar_Pervasives_Native.Some opt ->
           let uu___3 =
             let uu___4 =
               let uu___5 = update_option opt in alist_of_fstar_option uu___5 in
             ("option", uu___4) in
           FStar_Pervasives.Inr uu___3)
let run_module_lookup (st : FStarC_Interactive_Ide_Types.repl_state)
  (symbol : Prims.string) :
  (Prims.string,
    (Prims.string * (Prims.string * FStarC_Json.json) Prims.list))
    FStar_Pervasives.either=
  let query = FStarC_Util.split symbol "." in
  let uu___ =
    FStarC_Interactive_CompletionTable.find_module_or_ns
      st.FStarC_Interactive_Ide_Types.repl_names query in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      FStar_Pervasives.Inl "No such module or namespace"
  | FStar_Pervasives_Native.Some (FStarC_Interactive_CompletionTable.Module
      mod_info) ->
      let uu___1 =
        let uu___2 =
          FStarC_Interactive_CompletionTable.alist_of_mod_info mod_info in
        ("module", uu___2) in
      FStar_Pervasives.Inr uu___1
  | FStar_Pervasives_Native.Some
      (FStarC_Interactive_CompletionTable.Namespace ns_info) ->
      let uu___1 =
        let uu___2 =
          FStarC_Interactive_CompletionTable.alist_of_ns_info ns_info in
        ("namespace", uu___2) in
      FStar_Pervasives.Inr uu___1
let run_code_lookup (st : FStarC_Interactive_Ide_Types.repl_state)
  (symbol : Prims.string)
  (pos_opt :
    FStarC_Interactive_QueryHelper.position FStar_Pervasives_Native.option)
  (requested_info : Prims.string Prims.list)
  (symrange_opt : FStarC_Json.json FStar_Pervasives_Native.option) :
  (Prims.string,
    (Prims.string * (Prims.string * FStarC_Json.json) Prims.list))
    FStar_Pervasives.either=
  let uu___ = run_symbol_lookup st symbol pos_opt requested_info symrange_opt in
  match uu___ with
  | FStar_Pervasives.Inr alist -> FStar_Pervasives.Inr alist
  | FStar_Pervasives.Inl uu___1 ->
      let uu___2 = run_module_lookup st symbol in
      (match uu___2 with
       | FStar_Pervasives.Inr alist -> FStar_Pervasives.Inr alist
       | FStar_Pervasives.Inl err_msg ->
           FStar_Pervasives.Inl "No such symbol, module, or namespace.")
let run_lookup' (st : FStarC_Interactive_Ide_Types.repl_state)
  (symbol : Prims.string)
  (context : FStarC_Interactive_Ide_Types.lookup_context)
  (pos_opt :
    FStarC_Interactive_QueryHelper.position FStar_Pervasives_Native.option)
  (requested_info : Prims.string Prims.list)
  (symrange : FStarC_Json.json FStar_Pervasives_Native.option) :
  (Prims.string,
    (Prims.string * (Prims.string * FStarC_Json.json) Prims.list))
    FStar_Pervasives.either=
  match context with
  | FStarC_Interactive_Ide_Types.LKSymbolOnly ->
      run_symbol_lookup st symbol pos_opt requested_info symrange
  | FStarC_Interactive_Ide_Types.LKModule -> run_module_lookup st symbol
  | FStarC_Interactive_Ide_Types.LKOption -> run_option_lookup symbol
  | FStarC_Interactive_Ide_Types.LKCode ->
      run_code_lookup st symbol pos_opt requested_info symrange
let run_lookup (st : FStarC_Interactive_Ide_Types.repl_state)
  (symbol : Prims.string)
  (context : FStarC_Interactive_Ide_Types.lookup_context)
  (pos_opt :
    FStarC_Interactive_QueryHelper.position FStar_Pervasives_Native.option)
  (requested_info : Prims.string Prims.list)
  (symrange : FStarC_Json.json FStar_Pervasives_Native.option) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json Prims.list)
    * (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  try
    (fun uu___ ->
       match () with
       | () ->
           let uu___1 =
             run_lookup' st symbol context pos_opt requested_info symrange in
           (match uu___1 with
            | FStar_Pervasives.Inl err_msg ->
                (match symrange with
                 | FStar_Pervasives_Native.None ->
                     ((FStarC_Interactive_Ide_Types.QueryNOK,
                        [FStarC_Json.JsonStr err_msg]),
                       (FStar_Pervasives.Inl st))
                 | uu___2 ->
                     ((FStarC_Interactive_Ide_Types.QueryOK, []),
                       (FStar_Pervasives.Inl st)))
            | FStar_Pervasives.Inr (kind, info) ->
                ((FStarC_Interactive_Ide_Types.QueryOK,
                   [FStarC_Json.JsonAssoc
                      (("kind", (FStarC_Json.JsonStr kind)) :: info)]),
                  (FStar_Pervasives.Inl st)))) ()
  with
  | uu___ ->
      ((FStarC_Interactive_Ide_Types.QueryOK,
         [FStarC_Json.JsonStr
            (Prims.strcat "Lookup of " (Prims.strcat symbol " failed"))]),
        (FStar_Pervasives.Inl st))
let run_code_autocomplete (st : FStarC_Interactive_Ide_Types.repl_state)
  (search_term : Prims.string) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  let result = FStarC_Interactive_QueryHelper.ck_completion st search_term in
  let results =
    match result with
    | [] -> result
    | uu___ ->
        let result_correlator =
          {
            FStarC_Interactive_CompletionTable.completion_match_length =
              Prims.int_zero;
            FStarC_Interactive_CompletionTable.completion_candidate =
              search_term;
            FStarC_Interactive_CompletionTable.completion_annotation =
              "<search term>"
          } in
        FStarC_List.op_At result [result_correlator] in
  let js =
    FStarC_List.map
      FStarC_Interactive_CompletionTable.json_of_completion_result results in
  ((FStarC_Interactive_Ide_Types.QueryOK, (FStarC_Json.JsonList js)),
    (FStar_Pervasives.Inl st))
let run_module_autocomplete (st : FStarC_Interactive_Ide_Types.repl_state)
  (search_term : Prims.string) (modules : 'uuuuu) (namespaces : 'uuuuu1) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu2)
    FStar_Pervasives.either)=
  let needle = FStarC_Util.split search_term "." in
  let mods_and_nss =
    FStarC_Interactive_CompletionTable.autocomplete_mod_or_ns
      st.FStarC_Interactive_Ide_Types.repl_names needle
      (fun uu___ -> FStar_Pervasives_Native.Some uu___) in
  let json =
    FStarC_List.map
      FStarC_Interactive_CompletionTable.json_of_completion_result
      mods_and_nss in
  ((FStarC_Interactive_Ide_Types.QueryOK, (FStarC_Json.JsonList json)),
    (FStar_Pervasives.Inl st))
let candidates_of_fstar_option (match_len : Prims.int) (is_reset : 'uuuuu)
  (opt : fstar_option) :
  FStarC_Interactive_CompletionTable.completion_result Prims.list=
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
          Prims.strcat "("
            (Prims.strcat explanation
               (Prims.strcat " " (Prims.strcat opt_type ")"))) in
      FStarC_List.map
        (fun snippet ->
           {
             FStarC_Interactive_CompletionTable.completion_match_length =
               match_len;
             FStarC_Interactive_CompletionTable.completion_candidate =
               snippet;
             FStarC_Interactive_CompletionTable.completion_annotation = annot
           }) opt.opt_snippets
let run_option_autocomplete (st : 'uuuuu) (search_term : Prims.string)
  (is_reset : 'uuuuu1) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) * (
    'uuuuu, 'uuuuu2) FStar_Pervasives.either)=
  let uu___ = trim_option_name search_term in
  match uu___ with
  | ("--", trimmed_name) ->
      let matcher opt = FStarC_Util.starts_with opt.opt_name trimmed_name in
      let options = current_fstar_options matcher in
      let match_len = FStarC_String.length search_term in
      let collect_candidates = candidates_of_fstar_option match_len is_reset in
      let results = FStarC_List.concatMap collect_candidates options in
      let json =
        FStarC_List.map
          FStarC_Interactive_CompletionTable.json_of_completion_result
          results in
      ((FStarC_Interactive_Ide_Types.QueryOK, (FStarC_Json.JsonList json)),
        (FStar_Pervasives.Inl st))
  | (uu___1, uu___2) ->
      ((FStarC_Interactive_Ide_Types.QueryNOK,
         (FStarC_Json.JsonStr "Options should start with '--'")),
        (FStar_Pervasives.Inl st))
let run_autocomplete (st : FStarC_Interactive_Ide_Types.repl_state)
  (search_term : Prims.string)
  (context : FStarC_Interactive_Ide_Types.completion_context) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  match context with
  | FStarC_Interactive_Ide_Types.CKCode ->
      run_code_autocomplete st search_term
  | FStarC_Interactive_Ide_Types.CKOption is_reset ->
      run_option_autocomplete st search_term is_reset
  | FStarC_Interactive_Ide_Types.CKModuleOrNamespace (modules, namespaces) ->
      run_module_autocomplete st search_term modules namespaces
let run_and_rewind (st : FStarC_Interactive_Ide_Types.repl_state)
  (sigint_default : 'uuuuu)
  (task : FStarC_Interactive_Ide_Types.repl_state -> 'uuuuu) :
  ('uuuuu * (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu1)
    FStar_Pervasives.either)=
  let st1 =
    FStarC_Interactive_PushHelper.push_repl "run_and_rewind"
      (FStar_Pervasives_Native.Some FStarC_Interactive_Ide_Types.FullCheck)
      FStarC_Interactive_Ide_Types.Noop st in
  let results =
    try
      (fun uu___ ->
         match () with
         | () ->
             FStarC_Util.with_sigint_handler FStarC_Util.sigint_raise
               (fun uu___1 ->
                  let uu___2 = task st1 in FStar_Pervasives.Inl uu___2)) ()
    with | FStarC_Util.SigInt -> FStar_Pervasives.Inl sigint_default
    | e -> FStar_Pervasives.Inr e in
  let st2 = FStarC_Interactive_PushHelper.pop_repl "run_and_rewind" st1 in
  match results with
  | FStar_Pervasives.Inl results1 -> (results1, (FStar_Pervasives.Inl st2))
  | FStar_Pervasives.Inr e -> FStarC_Effect.raise e
let run_with_parsed_and_tc_term
  (st : FStarC_Interactive_Ide_Types.repl_state) (term : Prims.string)
  (line : 'uuuuu) (column : 'uuuuu1)
  (continuation :
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json))
  :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu2)
    FStar_Pervasives.either)=
  let dummy_let_fragment term1 =
    let dummy_decl = FStarC_Format.fmt1 "let __compute_dummy__ = (%s)" term1 in
    {
      FStarC_Parser_ParseIt.frag_fname = " input";
      FStarC_Parser_ParseIt.frag_text = dummy_decl;
      FStarC_Parser_ParseIt.frag_line = Prims.int_zero;
      FStarC_Parser_ParseIt.frag_col = Prims.int_zero
    } in
  let find_let_body ses =
    match ses with
    | {
        FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let
          {
            FStarC_Syntax_Syntax.lbs1 =
              (uu___,
               { FStarC_Syntax_Syntax.lbname = uu___1;
                 FStarC_Syntax_Syntax.lbunivs = univs;
                 FStarC_Syntax_Syntax.lbtyp = uu___2;
                 FStarC_Syntax_Syntax.lbeff = uu___3;
                 FStarC_Syntax_Syntax.lbdef = def;
                 FStarC_Syntax_Syntax.lbattrs = uu___4;
                 FStarC_Syntax_Syntax.lbpos = uu___5;_}::[]);
            FStarC_Syntax_Syntax.lids1 = uu___6;_};
        FStarC_Syntax_Syntax.sigrng = uu___7;
        FStarC_Syntax_Syntax.sigquals = uu___8;
        FStarC_Syntax_Syntax.sigmeta = uu___9;
        FStarC_Syntax_Syntax.sigattrs = uu___10;
        FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___11;
        FStarC_Syntax_Syntax.sigopts = uu___12;_}::[] ->
        FStar_Pervasives_Native.Some (univs, def)
    | uu___ -> FStar_Pervasives_Native.None in
  let parse frag =
    let uu___ =
      FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None
        (FStarC_Parser_ParseIt.Incremental frag) in
    match uu___ with
    | FStarC_Parser_ParseIt.IncrementalFragment (decls, uu___1, _err) ->
        let uu___2 = FStarC_List.map FStar_Pervasives_Native.fst decls in
        FStar_Pervasives_Native.Some uu___2
    | uu___1 -> FStar_Pervasives_Native.None in
  let desugar env decls =
    let uu___ =
      let uu___1 = FStarC_ToSyntax_ToSyntax.decls_to_sigelts decls in
      uu___1 env.FStarC_TypeChecker_Env.dsenv in
    FStar_Pervasives_Native.fst uu___ in
  let typecheck tcenv decls =
    let uu___ = FStarC_TypeChecker_Tc.tc_decls tcenv decls in
    match uu___ with | (ses, uu___1) -> ses in
  run_and_rewind st
    (FStarC_Interactive_Ide_Types.QueryNOK,
      (FStarC_Json.JsonStr "Computation interrupted"))
    (fun st1 ->
       let tcenv = st1.FStarC_Interactive_Ide_Types.repl_env in
       let frag = dummy_let_fragment term in
       let uu___ = parse frag in
       match uu___ with
       | FStar_Pervasives_Native.None ->
           (FStarC_Interactive_Ide_Types.QueryNOK,
             (FStarC_Json.JsonStr "Could not parse this term"))
       | FStar_Pervasives_Native.Some decls ->
           let aux uu___1 =
             let decls1 = desugar tcenv decls in
             let ses = typecheck tcenv decls1 in
             match find_let_body ses with
             | FStar_Pervasives_Native.None ->
                 (FStarC_Interactive_Ide_Types.QueryNOK,
                   (FStarC_Json.JsonStr
                      "Typechecking yielded an unexpected term"))
             | FStar_Pervasives_Native.Some (univs, def) ->
                 let uu___2 = FStarC_Syntax_Subst.open_univ_vars univs def in
                 (match uu___2 with
                  | (univs1, def1) ->
                      let tcenv1 =
                        FStarC_TypeChecker_Env.push_univ_vars tcenv univs1 in
                      continuation tcenv1 def1) in
           let uu___1 = FStarC_Options.trace_error () in
           if uu___1
           then aux ()
           else
             (try (fun uu___3 -> match () with | () -> aux ()) ()
              with
              | uu___3 ->
                  let uu___4 = FStarC_Errors.issue_of_exn uu___3 in
                  (match uu___4 with
                   | FStar_Pervasives_Native.Some issue ->
                       let uu___5 =
                         let uu___6 = FStarC_Errors.format_issue issue in
                         FStarC_Json.JsonStr uu___6 in
                       (FStarC_Interactive_Ide_Types.QueryNOK, uu___5)
                   | FStar_Pervasives_Native.None ->
                       FStarC_Effect.raise uu___3)))
let run_compute (st : FStarC_Interactive_Ide_Types.repl_state)
  (term : Prims.string)
  (rules :
    FStarC_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option)
  :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  let rules1 =
    FStarC_List.op_At
      (match rules with
       | FStar_Pervasives_Native.Some rules2 -> rules2
       | FStar_Pervasives_Native.None ->
           [FStarC_TypeChecker_Env.Beta;
           FStarC_TypeChecker_Env.Iota;
           FStarC_TypeChecker_Env.Zeta;
           FStarC_TypeChecker_Env.UnfoldUntil
             FStarC_Syntax_Syntax.delta_constant])
      [FStarC_TypeChecker_Env.Inlining;
      FStarC_TypeChecker_Env.Eager_unfolding;
      FStarC_TypeChecker_Env.DontUnfoldAttr
        [FStarC_Parser_Const.tac_opaque_attr];
      FStarC_TypeChecker_Env.Primops] in
  let normalize_term tcenv rules2 t =
    FStarC_TypeChecker_Normalize.normalize rules2 tcenv t in
  run_with_parsed_and_tc_term st term Prims.int_zero Prims.int_zero
    (fun tcenv def ->
       let normalized = normalize_term tcenv rules1 def in
       let uu___ =
         let uu___1 =
           FStarC_Interactive_QueryHelper.term_to_string tcenv normalized in
         FStarC_Json.JsonStr uu___1 in
       (FStarC_Interactive_Ide_Types.QueryOK, uu___))
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStarC_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let uu___is_NameContainsStr (projectee : search_term') : Prims.bool=
  match projectee with | NameContainsStr _0 -> true | uu___ -> false
let __proj__NameContainsStr__item___0 (projectee : search_term') :
  Prims.string= match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid (projectee : search_term') : Prims.bool=
  match projectee with | TypeContainsLid _0 -> true | uu___ -> false
let __proj__TypeContainsLid__item___0 (projectee : search_term') :
  FStarC_Ident.lid= match projectee with | TypeContainsLid _0 -> _0
let __proj__Mksearch_term__item__st_negate (projectee : search_term) :
  Prims.bool= match projectee with | { st_negate; st_term;_} -> st_negate
let __proj__Mksearch_term__item__st_term (projectee : search_term) :
  search_term'= match projectee with | { st_negate; st_term;_} -> st_term
let st_cost (uu___ : search_term') : Prims.int=
  match uu___ with
  | NameContainsStr str -> - (FStarC_String.length str)
  | TypeContainsLid lid -> Prims.int_one
type search_candidate =
  {
  sc_lid: FStarC_Ident.lid ;
  sc_typ:
    FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option FStarC_Effect.ref ;
  sc_fvars:
    FStarC_Ident.lid FStarC_RBSet.t FStar_Pervasives_Native.option
      FStarC_Effect.ref
    }
let __proj__Mksearch_candidate__item__sc_lid (projectee : search_candidate) :
  FStarC_Ident.lid=
  match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_lid
let __proj__Mksearch_candidate__item__sc_typ (projectee : search_candidate) :
  FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option FStarC_Effect.ref=
  match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_typ
let __proj__Mksearch_candidate__item__sc_fvars (projectee : search_candidate)
  :
  FStarC_Ident.lid FStarC_RBSet.t FStar_Pervasives_Native.option
    FStarC_Effect.ref=
  match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_fvars
let sc_of_lid (lid : FStarC_Ident.lid) : search_candidate=
  let uu___ = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let uu___1 = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  { sc_lid = lid; sc_typ = uu___; sc_fvars = uu___1 }
let sc_typ (tcenv : FStarC_TypeChecker_Env.env) (sc : search_candidate) :
  FStarC_Syntax_Syntax.typ=
  let uu___ = FStarC_Effect.op_Bang sc.sc_typ in
  match uu___ with
  | FStar_Pervasives_Native.Some t -> t
  | FStar_Pervasives_Native.None ->
      let typ =
        let uu___1 = FStarC_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
        match uu___1 with
        | FStar_Pervasives_Native.None ->
            FStarC_Syntax_Syntax.mk FStarC_Syntax_Syntax.Tm_unknown
              FStarC_Range_Type.dummyRange
        | FStar_Pervasives_Native.Some ((uu___2, typ1), uu___3) -> typ1 in
      (FStarC_Effect.op_Colon_Equals sc.sc_typ
         (FStar_Pervasives_Native.Some typ);
       typ)
let sc_fvars (tcenv : FStarC_TypeChecker_Env.env) (sc : search_candidate) :
  FStarC_Ident.lident FStarC_RBSet.t=
  let uu___ = FStarC_Effect.op_Bang sc.sc_fvars in
  match uu___ with
  | FStar_Pervasives_Native.Some fv -> fv
  | FStar_Pervasives_Native.None ->
      let fv =
        let uu___1 = sc_typ tcenv sc in FStarC_Syntax_Free.fvars uu___1 in
      (FStarC_Effect.op_Colon_Equals sc.sc_fvars
         (FStar_Pervasives_Native.Some fv);
       fv)
let json_of_search_result (tcenv : FStarC_TypeChecker_Env.env)
  (sc : search_candidate) : FStarC_Json.json=
  let typ_str =
    let uu___ = sc_typ tcenv sc in
    FStarC_Interactive_QueryHelper.term_to_string tcenv uu___ in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_Syntax_DsEnv.shorten_lid
              tcenv.FStarC_TypeChecker_Env.dsenv sc.sc_lid in
          FStarC_Ident.string_of_lid uu___4 in
        FStarC_Json.JsonStr uu___3 in
      ("lid", uu___2) in
    [uu___1; ("type", (FStarC_Json.JsonStr typ_str))] in
  FStarC_Json.JsonAssoc uu___
exception InvalidSearch of Prims.string 
let uu___is_InvalidSearch (projectee : Prims.exn) : Prims.bool=
  match projectee with | InvalidSearch uu___ -> true | uu___ -> false
let __proj__InvalidSearch__item__uu___ (projectee : Prims.exn) :
  Prims.string= match projectee with | InvalidSearch uu___ -> uu___
let run_search (st : FStarC_Interactive_Ide_Types.repl_state)
  (search_str : Prims.string) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  let tcenv = st.FStarC_Interactive_Ide_Types.repl_env in
  let st_matches candidate term =
    let found =
      match term.st_term with
      | NameContainsStr str ->
          let uu___ = FStarC_Ident.string_of_lid candidate.sc_lid in
          FStarC_Util.contains uu___ str
      | TypeContainsLid lid ->
          let uu___ = sc_fvars tcenv candidate in
          FStarC_Class_Setlike.mem ()
            (Obj.magic
               (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_fv)) lid
            (Obj.magic uu___) in
    found <> term.st_negate in
  let parse search_str1 =
    let parse_one term =
      let negate = FStarC_Util.starts_with term "-" in
      let term1 =
        if negate
        then FStarC_Util.substring_from term Prims.int_one
        else term in
      let beg_quote = FStarC_Util.starts_with term1 "\"" in
      let end_quote = FStarC_Util.ends_with term1 "\"" in
      let strip_quotes str =
        if (FStarC_String.length str) < (Prims.of_int (2))
        then FStarC_Effect.raise (InvalidSearch "Empty search term")
        else
          FStarC_Util.substring str Prims.int_one
            ((FStarC_String.length term1) - (Prims.of_int (2))) in
      let parsed =
        if beg_quote <> end_quote
        then
          let uu___ =
            let uu___1 =
              FStarC_Format.fmt1 "Improperly quoted search term: %s" term1 in
            InvalidSearch uu___1 in
          FStarC_Effect.raise uu___
        else
          if beg_quote
          then (let uu___1 = strip_quotes term1 in NameContainsStr uu___1)
          else
            (let lid = FStarC_Ident.lid_of_str term1 in
             let uu___2 =
               FStarC_Syntax_DsEnv.resolve_to_fully_qualified_name
                 tcenv.FStarC_TypeChecker_Env.dsenv lid in
             match uu___2 with
             | FStar_Pervasives_Native.None ->
                 let uu___3 =
                   let uu___4 =
                     FStarC_Format.fmt1 "Unknown identifier: %s" term1 in
                   InvalidSearch uu___4 in
                 FStarC_Effect.raise uu___3
             | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
      { st_negate = negate; st_term = parsed } in
    let terms = FStarC_List.map parse_one (FStarC_Util.split search_str1 " ") in
    let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
    FStarC_Util.sort_with cmp terms in
  let pprint_one term =
    let uu___ =
      match term.st_term with
      | NameContainsStr s -> FStarC_Format.fmt1 "\"%s\"" s
      | TypeContainsLid l ->
          let uu___1 = FStarC_Ident.string_of_lid l in
          FStarC_Format.fmt1 "%s" uu___1 in
    Prims.strcat (if term.st_negate then "-" else "") uu___ in
  let results =
    try
      (fun uu___ ->
         match () with
         | () ->
             let terms = parse search_str in
             let all_lidents = FStarC_TypeChecker_Env.lidents tcenv in
             let all_candidates = FStarC_List.map sc_of_lid all_lidents in
             let matches_all candidate =
               FStarC_List.for_all (st_matches candidate) terms in
             let cmp r1 r2 =
               let uu___1 = FStarC_Ident.string_of_lid r1.sc_lid in
               let uu___2 = FStarC_Ident.string_of_lid r2.sc_lid in
               FStarC_Util.compare uu___1 uu___2 in
             let results1 = FStarC_List.filter matches_all all_candidates in
             let sorted = FStarC_Util.sort_with cmp results1 in
             let js = FStarC_List.map (json_of_search_result tcenv) sorted in
             (match results1 with
              | [] ->
                  let kwds =
                    let uu___1 = FStarC_List.map pprint_one terms in
                    FStarC_Util.concat_l " " uu___1 in
                  let uu___1 =
                    let uu___2 =
                      FStarC_Format.fmt1 "No results found for query [%s]"
                        kwds in
                    InvalidSearch uu___2 in
                  FStarC_Effect.raise uu___1
              | uu___1 ->
                  (FStarC_Interactive_Ide_Types.QueryOK,
                    (FStarC_Json.JsonList js)))) ()
    with
    | InvalidSearch s ->
        (FStarC_Interactive_Ide_Types.QueryNOK, (FStarC_Json.JsonStr s)) in
  (results, (FStar_Pervasives.Inl st))
let run_format_code (st : FStarC_Interactive_Ide_Types.repl_state)
  (code : Prims.string) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
    (FStarC_Interactive_Ide_Types.repl_state, 'uuuuu)
    FStar_Pervasives.either)=
  let code_or_err = FStarC_Interactive_Incremental.format_code st code in
  match code_or_err with
  | FStar_Pervasives.Inl code1 ->
      let result =
        FStarC_Json.JsonAssoc
          [("formatted-code", (FStarC_Json.JsonStr code1))] in
      ((FStarC_Interactive_Ide_Types.QueryOK, result),
        (FStar_Pervasives.Inl st))
  | FStar_Pervasives.Inr issue ->
      let result =
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_List.map json_of_issue issue in
              FStarC_Json.JsonList uu___3 in
            ("formatted-code-issue", uu___2) in
          [uu___1] in
        FStarC_Json.JsonAssoc uu___ in
      ((FStarC_Interactive_Ide_Types.QueryNOK, result),
        (FStar_Pervasives.Inl st))
let as_json_list
  (q :
    ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json) *
      (FStarC_Interactive_Ide_Types.repl_state, Prims.int)
      FStar_Pervasives.either))
  :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json Prims.list)
    * (FStarC_Interactive_Ide_Types.repl_state, Prims.int)
    FStar_Pervasives.either)=
  let uu___ = q in match uu___ with | ((q1, j), s) -> ((q1, [j]), s)
type run_query_result =
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json Prims.list)
    * (FStarC_Interactive_Ide_Types.repl_state, Prims.int)
    FStar_Pervasives.either)
let maybe_cancel_queries (st : FStarC_Interactive_Ide_Types.repl_state)
  (l : FStarC_Interactive_Ide_Types.query Prims.list) :
  (FStarC_Interactive_Ide_Types.query Prims.list *
    FStarC_Interactive_Ide_Types.repl_state)=
  let log_cancellation l1 =
    let uu___ = FStarC_Effect.op_Bang dbg in
    if uu___
    then
      FStarC_List.iter
        (fun q ->
           let uu___1 = FStarC_Interactive_Ide_Types.query_to_string q in
           FStarC_Format.print1 "Cancelling query: %s\n" uu___1) l1
    else () in
  match st.FStarC_Interactive_Ide_Types.repl_buffered_input_queries with
  | {
      FStarC_Interactive_Ide_Types.qq = FStarC_Interactive_Ide_Types.Cancel p;
      FStarC_Interactive_Ide_Types.qid = uu___;_}::rest ->
      let st1 =
        {
          FStarC_Interactive_Ide_Types.repl_line =
            (st.FStarC_Interactive_Ide_Types.repl_line);
          FStarC_Interactive_Ide_Types.repl_column =
            (st.FStarC_Interactive_Ide_Types.repl_column);
          FStarC_Interactive_Ide_Types.repl_fname =
            (st.FStarC_Interactive_Ide_Types.repl_fname);
          FStarC_Interactive_Ide_Types.repl_deps_stack =
            (st.FStarC_Interactive_Ide_Types.repl_deps_stack);
          FStarC_Interactive_Ide_Types.repl_curmod =
            (st.FStarC_Interactive_Ide_Types.repl_curmod);
          FStarC_Interactive_Ide_Types.repl_env =
            (st.FStarC_Interactive_Ide_Types.repl_env);
          FStarC_Interactive_Ide_Types.repl_stdin =
            (st.FStarC_Interactive_Ide_Types.repl_stdin);
          FStarC_Interactive_Ide_Types.repl_names =
            (st.FStarC_Interactive_Ide_Types.repl_names);
          FStarC_Interactive_Ide_Types.repl_buffered_input_queries = rest;
          FStarC_Interactive_Ide_Types.repl_lang =
            (st.FStarC_Interactive_Ide_Types.repl_lang)
        } in
      (match p with
       | FStar_Pervasives_Native.None -> (log_cancellation l; ([], st1))
       | FStar_Pervasives_Native.Some p1 ->
           let query_ahead_of p2 q =
             let uu___1 = p2 in
             match uu___1 with
             | (uu___2, l1, c) ->
                 (match q.FStarC_Interactive_Ide_Types.qq with
                  | FStarC_Interactive_Ide_Types.Push pq ->
                      pq.FStarC_Interactive_Ide_Types.push_line >= l1
                  | uu___3 -> false) in
           let l1 =
             let uu___1 = FStarC_Util.prefix_until (query_ahead_of p1) l in
             match uu___1 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some (l2, q, qs) ->
                 (log_cancellation (q :: qs); l2) in
           (l1, st1))
  | uu___ -> (l, st)
let rec fold_query
  (f :
    FStarC_Interactive_Ide_Types.repl_state ->
      FStarC_Interactive_Ide_Types.query -> run_query_result)
  (l : FStarC_Interactive_Ide_Types.query Prims.list)
  (st : FStarC_Interactive_Ide_Types.repl_state) : run_query_result=
  match l with
  | [] ->
      ((FStarC_Interactive_Ide_Types.QueryOK, []), (FStar_Pervasives.Inl st))
  | q::l1 ->
      let uu___ = f st q in
      (match uu___ with
       | ((status, responses), st') ->
           (FStarC_List.iter
              (write_response q.FStarC_Interactive_Ide_Types.qid status)
              responses;
            (match (status, st') with
             | (FStarC_Interactive_Ide_Types.QueryOK, FStar_Pervasives.Inl
                st1) ->
                 let st2 = buffer_input_queries st1 in
                 let uu___2 = maybe_cancel_queries st2 l1 in
                 (match uu___2 with | (l2, st3) -> fold_query f l2 st3)
             | uu___2 -> ((status, []), st'))))
let validate_query (st : FStarC_Interactive_Ide_Types.repl_state)
  (q : FStarC_Interactive_Ide_Types.query) :
  FStarC_Interactive_Ide_Types.query=
  match q.FStarC_Interactive_Ide_Types.qq with
  | FStarC_Interactive_Ide_Types.Push
      {
        FStarC_Interactive_Ide_Types.push_kind =
          FStarC_Interactive_Ide_Types.SyntaxCheck;
        FStarC_Interactive_Ide_Types.push_line = uu___;
        FStarC_Interactive_Ide_Types.push_column = uu___1;
        FStarC_Interactive_Ide_Types.push_peek_only = false;
        FStarC_Interactive_Ide_Types.push_code_or_decl = uu___2;_}
      ->
      {
        FStarC_Interactive_Ide_Types.qq =
          (FStarC_Interactive_Ide_Types.ProtocolViolation
             "Cannot use 'kind': 'syntax' with 'query': 'push'");
        FStarC_Interactive_Ide_Types.qid =
          (q.FStarC_Interactive_Ide_Types.qid)
      }
  | uu___ ->
      (match st.FStarC_Interactive_Ide_Types.repl_curmod with
       | FStar_Pervasives_Native.None when
           FStarC_Interactive_Ide_Types.query_needs_current_module
             q.FStarC_Interactive_Ide_Types.qq
           ->
           {
             FStarC_Interactive_Ide_Types.qq =
               (FStarC_Interactive_Ide_Types.GenericError
                  "Current module unset");
             FStarC_Interactive_Ide_Types.qid =
               (q.FStarC_Interactive_Ide_Types.qid)
           }
       | uu___1 -> q)
let rec run_query (st : FStarC_Interactive_Ide_Types.repl_state)
  (q : FStarC_Interactive_Ide_Types.query) :
  ((FStarC_Interactive_Ide_Types.query_status * FStarC_Json.json Prims.list)
    * (FStarC_Interactive_Ide_Types.repl_state, Prims.int)
    FStar_Pervasives.either)=
  match q.FStarC_Interactive_Ide_Types.qq with
  | FStarC_Interactive_Ide_Types.Exit -> as_json_list (run_exit st)
  | FStarC_Interactive_Ide_Types.DescribeProtocol ->
      as_json_list (run_describe_protocol st)
  | FStarC_Interactive_Ide_Types.DescribeRepl ->
      let uu___ = run_describe_repl st in as_json_list uu___
  | FStarC_Interactive_Ide_Types.GenericError message ->
      as_json_list (run_generic_error st message)
  | FStarC_Interactive_Ide_Types.ProtocolViolation query ->
      as_json_list (run_protocol_violation st query)
  | FStarC_Interactive_Ide_Types.Segment c ->
      let uu___ = run_segment st c in as_json_list uu___
  | FStarC_Interactive_Ide_Types.VfsAdd (fname, contents) ->
      let uu___ = run_vfs_add st fname contents in as_json_list uu___
  | FStarC_Interactive_Ide_Types.Push pquery ->
      let uu___ = run_push st pquery in as_json_list uu___
  | FStarC_Interactive_Ide_Types.PushPartialCheckedFile decl_name ->
      let uu___ = run_load_partial_file st decl_name in as_json_list uu___
  | FStarC_Interactive_Ide_Types.Pop ->
      let uu___ = run_pop st in as_json_list uu___
  | FStarC_Interactive_Ide_Types.FullBuffer (code, full_kind, with_symbols)
      ->
      (write_full_buffer_fragment_progress
         FStarC_Interactive_Incremental.FullBufferStarted;
       (let uu___1 =
          FStarC_Interactive_Incremental.run_full_buffer st
            q.FStarC_Interactive_Ide_Types.qid code full_kind with_symbols
            write_full_buffer_fragment_progress in
        match uu___1 with
        | (queries, issues) ->
            (FStarC_List.iter
               (write_response q.FStarC_Interactive_Ide_Types.qid
                  FStarC_Interactive_Ide_Types.QueryOK) issues;
             (let res = fold_query validate_and_run_query queries st in
              write_full_buffer_fragment_progress
                FStarC_Interactive_Incremental.FullBufferFinished;
              res))))
  | FStarC_Interactive_Ide_Types.AutoComplete (search_term1, context) ->
      let uu___ = run_autocomplete st search_term1 context in
      as_json_list uu___
  | FStarC_Interactive_Ide_Types.Lookup
      (symbol, context, pos_opt, rq_info, symrange) ->
      run_lookup st symbol context pos_opt rq_info symrange
  | FStarC_Interactive_Ide_Types.Compute (term, rules) ->
      let uu___ = run_compute st term rules in as_json_list uu___
  | FStarC_Interactive_Ide_Types.Search term ->
      let uu___ = run_search st term in as_json_list uu___
  | FStarC_Interactive_Ide_Types.Callback f -> f st
  | FStarC_Interactive_Ide_Types.Format code ->
      let uu___ = run_format_code st code in as_json_list uu___
  | FStarC_Interactive_Ide_Types.RestartSolver ->
      (((st.FStarC_Interactive_Ide_Types.repl_env).FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.refresh
         FStar_Pervasives_Native.None;
       ((FStarC_Interactive_Ide_Types.QueryOK, []),
         (FStar_Pervasives.Inl st)))
  | FStarC_Interactive_Ide_Types.Cancel uu___ ->
      ((FStarC_Interactive_Ide_Types.QueryOK, []), (FStar_Pervasives.Inl st))
and validate_and_run_query (st : FStarC_Interactive_Ide_Types.repl_state)
  (query : FStarC_Interactive_Ide_Types.query) : run_query_result=
  let query1 = validate_query st query in
  FStarC_Effect.op_Colon_Equals repl_current_qid
    (FStar_Pervasives_Native.Some (query1.FStarC_Interactive_Ide_Types.qid));
  (let uu___2 = FStarC_Effect.op_Bang dbg in
   if uu___2
   then
     let uu___3 = FStarC_Interactive_Ide_Types.query_to_string query1 in
     FStarC_Format.print2 "Running query %s: %s\n"
       query1.FStarC_Interactive_Ide_Types.qid uu___3
   else ());
  run_query st query1
let js_repl_eval (st : FStarC_Interactive_Ide_Types.repl_state)
  (query : FStarC_Interactive_Ide_Types.query) :
  (FStarC_Json.json Prims.list * (FStarC_Interactive_Ide_Types.repl_state,
    Prims.int) FStar_Pervasives.either)=
  let uu___ = validate_and_run_query st query in
  match uu___ with
  | ((status, responses), st_opt) ->
      let js_responses =
        FStarC_List.map
          (json_of_response query.FStarC_Interactive_Ide_Types.qid status)
          responses in
      (js_responses, st_opt)
let js_repl_eval_js (st : FStarC_Interactive_Ide_Types.repl_state)
  (query_js : FStarC_Json.json) :
  (FStarC_Json.json Prims.list * (FStarC_Interactive_Ide_Types.repl_state,
    Prims.int) FStar_Pervasives.either)=
  let uu___ = deserialize_interactive_query st query_js in
  js_repl_eval st uu___
let js_repl_eval_str (st : FStarC_Interactive_Ide_Types.repl_state)
  (query_str : Prims.string) :
  (Prims.string Prims.list * (FStarC_Interactive_Ide_Types.repl_state,
    Prims.int) FStar_Pervasives.either)=
  let uu___ =
    let uu___1 = parse_interactive_query st query_str in
    js_repl_eval st uu___1 in
  match uu___ with
  | (js_response, st_opt) ->
      let uu___1 = FStarC_List.map FStarC_Json.string_of_json js_response in
      (uu___1, st_opt)
let js_repl_init_opts (uu___ : unit) : unit=
  let uu___1 = FStarC_Options.parse_cmd_line () in
  match uu___1 with
  | (res, fnames) ->
      (match res with
       | FStarC_Getopt.Error (msg, uu___2) ->
           failwith (Prims.strcat "repl_init: " msg)
       | FStarC_Getopt.Success ->
           (match fnames with
            | [] ->
                failwith "repl_init: No file name given in --ide invocation"
            | h::uu___2::uu___3 ->
                failwith
                  "repl_init: Too many file names given in --ide invocation"
            | uu___2 -> ()))
let rec go (st : FStarC_Interactive_Ide_Types.repl_state) : Prims.int=
  let uu___ = read_interactive_query st in
  match uu___ with
  | FStar_Pervasives_Native.None -> Prims.int_zero
  | FStar_Pervasives_Native.Some (query, st1) ->
      let uu___1 = validate_and_run_query st1 query in
      (match uu___1 with
       | ((status, responses), state_opt) ->
           (FStarC_List.iter
              (write_response query.FStarC_Interactive_Ide_Types.qid status)
              responses;
            (match state_opt with
             | FStar_Pervasives.Inl st' -> go st'
             | FStar_Pervasives.Inr exitcode -> exitcode)))
let interactive_error_handler : FStarC_Errors.error_handler=
  FStarC_Errors.mk_catch_handler ()
let interactive_printer (printer : FStarC_Json.json -> unit) :
  FStarC_Format.printer=
  {
    FStarC_Format.printer_prinfo =
      (fun s -> forward_message printer "info" (FStarC_Json.JsonStr s));
    FStarC_Format.printer_prwarning =
      (fun s -> forward_message printer "warning" (FStarC_Json.JsonStr s));
    FStarC_Format.printer_prerror =
      (fun s -> forward_message printer "error" (FStarC_Json.JsonStr s));
    FStarC_Format.printer_prgeneric =
      (fun label get_string get_json ->
         let uu___ = get_json () in forward_message printer label uu___)
  }
let install_ide_mode_hooks (printer : FStarC_Json.json -> unit) : unit=
  FStarC_Format.set_printer (interactive_printer printer);
  FStarC_Errors.set_handler interactive_error_handler
let build_initial_repl_state (filename : Prims.string) :
  FStarC_Interactive_Ide_Types.repl_state=
  (let uu___1 = FStarC_Parser_Dep.lowercase_module_name filename in
   FStarC_Options.add_verify_module uu___1);
  (let env =
     let uu___1 = FStarC_Parser_Dep.empty_deps [filename] in
     FStarC_Universal.init_env uu___1 in
   let env1 =
     let uu___1 = FStarC_Interactive_Ide_Types.initial_range filename in
     FStarC_TypeChecker_Env.set_range env uu___1 in
   FStarC_Options.set_ide_filename filename;
   (let uu___2 = FStarC_Util.open_stdin () in
    {
      FStarC_Interactive_Ide_Types.repl_line = Prims.int_one;
      FStarC_Interactive_Ide_Types.repl_column = Prims.int_zero;
      FStarC_Interactive_Ide_Types.repl_fname = filename;
      FStarC_Interactive_Ide_Types.repl_deps_stack = [];
      FStarC_Interactive_Ide_Types.repl_curmod = FStar_Pervasives_Native.None;
      FStarC_Interactive_Ide_Types.repl_env = env1;
      FStarC_Interactive_Ide_Types.repl_stdin = uu___2;
      FStarC_Interactive_Ide_Types.repl_names =
        FStarC_Interactive_CompletionTable.empty;
      FStarC_Interactive_Ide_Types.repl_buffered_input_queries = [];
      FStarC_Interactive_Ide_Types.repl_lang = []
    }))
let interactive_mode' (init_st : FStarC_Interactive_Ide_Types.repl_state) :
  unit=
  write_hello ();
  (let exit_code =
     let fn =
       let uu___1 = FStarC_Options.file_list () in FStarC_List.hd uu___1 in
     FStarC_SMTEncoding_Solver.with_hints_db fn (fun uu___1 -> go init_st) in
   if exit_code <> Prims.int_zero then FStarC_Effect.exit exit_code else ())
let interactive_mode (filename : Prims.string) : unit=
  install_ide_mode_hooks FStarC_Interactive_JsonHelper.write_json;
  FStarC_Util.set_sigint_handler FStarC_Util.sigint_ignore;
  (let uu___3 =
     let uu___4 = FStarC_Options.codegen () in
     FStar_Pervasives_Native.uu___is_Some uu___4 in
   if uu___3
   then
     FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_IDEIgnoreCodeGen ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
       (Obj.magic "--ide: ignoring --codegen")
   else ());
  (let init = build_initial_repl_state filename in
   let uu___3 = FStarC_Options.trace_error () in
   if uu___3
   then interactive_mode' init
   else
     (try (fun uu___5 -> match () with | () -> interactive_mode' init) ()
      with
      | uu___5 ->
          (FStarC_Errors.set_handler FStarC_Errors.default_handler;
           FStarC_Effect.raise uu___5)))
