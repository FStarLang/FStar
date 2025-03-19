(*
   Copyright 2008-2016  Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStarC.Interactive.Ide
open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Range
open FStarC.Util
open FStarC.Getopt
open FStarC.Ident
open FStarC.Errors
open FStarC.Interactive.JsonHelper
open FStarC.Interactive.QueryHelper
open FStarC.Interactive.PushHelper
open FStarC.Interactive.Ide.Types
module BU = FStarC.Util

open FStarC.Class.Show

let dbg = Debug.get_toggle "IDE"

open FStarC.Universal
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.Interactive
open FStarC.Parser.ParseIt
open FStarC.Interactive.Ide.Types
module SS = FStarC.Syntax.Syntax
module DsEnv = FStarC.Syntax.DsEnv
module TcErr = FStarC.TypeChecker.Err
module TcEnv = FStarC.TypeChecker.Env
module CTable = FStarC.Interactive.CompletionTable
module QH = FStarC.Interactive.QueryHelper

// NOTE! This is not FStarC.Errors.json_of_issue
let json_of_issue = FStarC.Interactive.Ide.Types.json_of_issue

let with_captured_errors' env sigint_handler f =
  try
    Util.with_sigint_handler sigint_handler (fun _ -> f env)
  with
  | Failure (msg) ->
    let msg = "ASSERTION FAILURE: " ^ msg ^ "\n" ^
              "F* may be in an inconsistent state.\n" ^
              "Please file a bug report, ideally with a " ^
              "minimized version of the program that triggered the error." in
    // Make sure the user sees the error, even if it happened transiently while
    // running an automatic syntax checker like FlyCheck.
    Errors.log_issue env Errors.Error_IDEAssertionFailure msg;
    None

  | Util.SigInt ->
    Util.print_string "Interrupted"; None

  | Error (e, msg, r, ctx) ->
    TcErr.add_errors env [(e, msg, r, ctx)];
    None

  | Stop ->
    None

let with_captured_errors env sigint_handler f =
  if Options.trace_error () then f env
  else with_captured_errors' env sigint_handler f
  
(** Tasks describing each snapshot of the REPL state. **)

type env_t = TcEnv.env

let repl_current_qid : ref (option string) = mk_ref None // For messages

(** Check whether users can issue further ``pop`` commands. **)
let nothing_left_to_pop st =
  (* The first ``length st.repl_deps_stack`` entries in ``repl_stack`` are
     dependency-loading entries, which the user may not pop (since they didn't
     push them). *)
  List.length !repl_stack = List.length st.repl_deps_stack

(*********************)
(* Dependency checks *)
(*********************)

(** Push, run `task`, and pop if it fails.

If `must_rollback` is set, always pop.  Returns a pair: a boolean indicating
success, and a new REPL state. **)
let run_repl_transaction st push_kind must_rollback task =
  let st = push_repl "run_repl_transaction" push_kind task st in
  let env, finish_name_tracking = track_name_changes st.repl_env in // begin name tracking …

  let check_success () =
    get_err_count () = 0 && not must_rollback in

  // Run the task (and capture errors)
  let curmod, env, success, lds =
    match with_captured_errors env Util.sigint_raise
              (fun env -> Some <| run_repl_task st.repl_curmod env task st.repl_lang) with
    | Some (curmod, env, lds) when check_success () -> curmod, env, true, lds
    | _ -> st.repl_curmod, env, false, [] in

  let env, name_events = finish_name_tracking env in //  …end name tracking
  let st =
    if success then
      let st = { st with repl_env = env; repl_curmod = curmod; repl_lang=List.rev lds@st.repl_lang } in
      commit_name_tracking st name_events
    else
      pop_repl "run_repl_transaction" st in

  (success, st)

(** Load dependencies described by `tasks`.

Returns a new REPL state, wrapped in ``Inl`` to indicate complete success or
``Inr`` to indicate a partial failure.  That new state has an updated
``repl_deps_stack``, containing loaded dependencies in reverse order compared to
the original list of tasks: the first dependencies (prims, ...) come first; the
current file's interface comes last.

The original value of the ``repl_deps_stack`` field in ``st`` is used to skip
already completed tasks.

This function is stateful: it uses ``push_repl`` and ``pop_repl``.

`progress_callback` is called once per task, right before the task is run. **)
let run_repl_ld_transactions (st: repl_state) (tasks: list repl_task)
                             (progress_callback: repl_task -> unit) =
  let debug verb task =
    if !dbg then
      Util.print2 "%s %s" verb (string_of_repl_task task) in

  (* Run as many ``pop_repl`` as there are entries in the input stack.
  Elements of the input stack are expected to match the topmost ones of
  ``!repl_stack`` *)
  let rec revert_many st = function
    | [] -> st
    | (_id, (task, _st')) :: entries ->
      //NS: this assertion has been failing for a while in debug mode; not sure why
      assert (task = fst (snd (List.hd !repl_stack)));
      debug "Reverting" task;
      let st' = pop_repl "run_repl_ls_transactions" st in
      let dep_graph = FStarC.TypeChecker.Env.dep_graph st.repl_env in
      let st' = {st' with repl_env=FStarC.TypeChecker.Env.set_dep_graph st'.repl_env dep_graph} in
      revert_many st' entries in

  let rec aux (st: repl_state)
              (tasks: list repl_task)
              (previous: list repl_stack_entry_t) =
    match tasks, previous with
    // All done: return the final state.
    | [], [] ->
      Inl st

    // We have more dependencies to load, and no previously loaded dependencies:
    // run ``task`` and record the updated dependency stack in ``st``.
    | task :: tasks, [] ->
      debug "Loading" task;
      progress_callback task;
      Options.restore_cmd_line_options false |> ignore;
      let timestamped_task = update_task_timestamps task in
      let push_kind = if Options.lax () then LaxCheck else FullCheck in
      let success, st = run_repl_transaction st (Some push_kind) false timestamped_task in
      if success then aux ({ st with repl_deps_stack = !repl_stack }) tasks []
      else Inr st

    // We've already run ``task`` previously, and no update is needed: skip.
    | task :: tasks, prev :: previous
        when fst (snd prev) = update_task_timestamps task ->
      debug "Skipping" task;
      aux st tasks previous

    // We have a timestamp mismatch or a new dependency:
    // revert now-obsolete dependencies and resume loading.
    | tasks, previous ->
      aux (revert_many st previous) tasks [] in

  aux st tasks (List.rev st.repl_deps_stack)

let wrap_js_failure qid expected got =
  { qid = qid;
    qq = ProtocolViolation (Util.format2 "JSON decoding failed: expected %s, got %s"
                            expected (json_debug got)) }

let unpack_interactive_query json =
  let assoc errloc key a =
    match try_assoc key a with
    | Some v -> v
    | None -> raise (InvalidQuery (Util.format2 "Missing key [%s] in %s." key errloc)) in

  let request = json |> js_assoc in

  let qid = assoc "query" "query-id" request |> js_str in
  try
    let query = assoc "query" "query" request |> js_str in
    let args = assoc "query" "args" request |> js_assoc in

    let arg k = assoc "[args]" k args in
    let try_arg k =
      match try_assoc k args with
      | Some JsonNull -> None
      | other -> other in

    let read_position err loc =
        assoc err "filename" loc |> js_str,
        assoc err "line" loc |> js_int,
        assoc err "column" loc |> js_int
    in
    let read_to_position () =
      let to_pos = arg "to-position" |> js_assoc in
      "<input>",
      assoc  "to-position.line" "line" to_pos  |> js_int, 
      assoc "to-position.column" "column"  to_pos |> js_int
    in
    let parse_full_buffer_kind (kind:string) =
      match kind with
      | "full" -> Full
      | "lax" -> Lax
      | "cache" -> Cache
      | "reload-deps" -> ReloadDeps
      | "verify-to-position" -> VerifyToPosition (read_to_position ())
      | "lax-to-position" -> LaxToPosition (read_to_position ())
      | _ -> raise (InvalidQuery "Invalid full-buffer kind")
    in
    { qid = qid;
      qq = match query with
           | "exit" -> Exit
           | "pop" -> Pop
           | "describe-protocol" -> DescribeProtocol
           | "describe-repl" -> DescribeRepl
           | "segment" -> Segment (arg "code" |> js_str)
           | "peek" | "push" -> Push ({ push_kind = arg "kind" |> js_pushkind;
                                       push_code_or_decl = Inl (arg "code" |> js_str);
                                       push_line = arg "line" |> js_int;
                                       push_column = arg "column" |> js_int;
                                       push_peek_only = query = "peek" })
           | "push-partial-checked-file" -> PushPartialCheckedFile (arg "until-lid" |> js_str)
           | "full-buffer" -> FullBuffer (arg "code" |> js_str,
                                          parse_full_buffer_kind (arg "kind" |> js_str), 
                                          arg "with-symbols" |> js_bool)
           | "autocomplete" -> AutoComplete (arg "partial-symbol" |> js_str,
                                            try_arg "context" |> js_optional_completion_context)
           | "lookup" -> Lookup (arg "symbol" |> js_str,
                                try_arg "context" |> js_optional_lookup_context,
                                try_arg "location"
                                  |> Util.map_option js_assoc
                                  |> Util.map_option (read_position "[location]"),
                                arg "requested-info" |> js_list js_str,
                                try_arg "symbol-range")
           | "compute" -> Compute (arg "term" |> js_str,
                                  try_arg "rules"
                                    |> Util.map_option (js_list js_reductionrule))
           | "search" -> Search (arg "terms" |> js_str)
           | "vfs-add" -> VfsAdd (try_arg "filename" |> Util.map_option js_str,
                                 arg "contents" |> js_str)
           | "format" -> Format (arg "code" |> js_str)
           | "restart-solver" -> RestartSolver
           | "cancel" -> Cancel (Some("<input>", arg "cancel-line" |> js_int, arg "cancel-column" |> js_int))
           | _ -> ProtocolViolation (Util.format1 "Unknown query '%s'" query) }
  with
  | InvalidQuery msg -> { qid = qid; qq = ProtocolViolation msg }
  | UnexpectedJsonType (expected, got) -> wrap_js_failure qid expected got

let deserialize_interactive_query js_query =
  try
    unpack_interactive_query js_query
  with
  | InvalidQuery msg -> { qid = "?"; qq = ProtocolViolation msg }
  | UnexpectedJsonType (expected, got) -> wrap_js_failure "?" expected got

let parse_interactive_query query_str : query =
  match json_of_string query_str with
  | None -> { qid = "?"; qq = ProtocolViolation "Json parsing failed." }
  | Some request -> deserialize_interactive_query request

let buffer_input_queries (st:repl_state) : repl_state =
  let rec aux qs (st:repl_state) : repl_state =
    let done qs st =
        {st with repl_buffered_input_queries =
                 st.repl_buffered_input_queries @ List.rev qs}
    in
    if not (Util.poll_stdin (float_of_string "0.0"))
    then done qs st
    else (
      match Util.read_line st.repl_stdin with
      | None ->
        done qs st

      | Some line -> 
        let q = parse_interactive_query line in
        match q.qq with
        | Cancel _ -> 
          //Cancel drains all buffered queries
          {st with repl_buffered_input_queries = [q] }
        | _ -> aux (q :: qs) st
    )
  in
  aux [] st

let read_interactive_query (st:repl_state) : query & repl_state =
    match st.repl_buffered_input_queries with
    | [] -> (
      match Util.read_line st.repl_stdin with
      | None -> exit 0
      | Some line -> parse_interactive_query line, st
    )
    | q :: qs ->
      q, { st with repl_buffered_input_queries = qs }
  
let json_of_opt json_of_a opt_a =
  Util.dflt JsonNull (Util.map_option json_of_a opt_a)

let alist_of_symbol_lookup_result lr symbol symrange_opt=
  [("name", JsonStr lr.slr_name);
   ("defined-at", json_of_opt (fun r -> json_of_def_range (Range.refind_range r)) lr.slr_def_range);
   ("type", json_of_opt JsonStr lr.slr_typ);
   ("documentation", json_of_opt JsonStr lr.slr_doc);
   ("definition", json_of_opt JsonStr lr.slr_def)] @ (
    // echo back the symbol-range and symbol, if symbol-range was provided
    // (don't include it otherwise, for backwards compat with fstar-mode.el)
    match symrange_opt with
    | None -> []
    | Some symrange -> 
     [("symbol-range", json_of_opt (fun x -> x) symrange_opt);
      ("symbol", JsonStr symbol)]
  )

let alist_of_protocol_info =
  let js_version = JsonInt interactive_protocol_vernum in
  let js_features = JsonList <| List.map JsonStr interactive_protocol_features in
  [("version", js_version); ("features", js_features)]

type fstar_option_permission_level =
| OptSet
| OptReadOnly

let string_of_option_permission_level = function
  | OptSet -> ""
  | OptReadOnly -> "read-only"

type fstar_option =
  { opt_name: string;
    opt_sig: string;
    opt_value: Options.option_val;
    opt_default: Options.option_val;
    opt_type: Options.opt_type;
    opt_snippets: list string;
    opt_documentation: option string;
    opt_permission_level: fstar_option_permission_level }

let rec kind_of_fstar_option_type = function
  | Options.Const _ -> "flag"
  | Options.IntStr _ -> "int"
  | Options.BoolStr -> "bool"
  | Options.PathStr _ -> "path"
  | Options.SimpleStr _ -> "string"
  | Options.EnumStr _ -> "enum"
  | Options.OpenEnumStr _ -> "open enum"
  | Options.PostProcessed (_, typ)
  | Options.Accumulated typ
  | Options.ReverseAccumulated typ
  | Options.WithSideEffect (_, typ) -> kind_of_fstar_option_type typ

let snippets_of_fstar_option name typ =
  let mk_field field_name =
    "${" ^ field_name ^ "}" in
  let mk_snippet name argstring =
    "--" ^ name ^ (if argstring <> "" then " " ^ argstring else "") in
  let rec arg_snippets_of_type typ =
    match typ with
    | Options.Const _ -> [""]
    | Options.BoolStr -> ["true"; "false"]
    | Options.IntStr desc
    | Options.PathStr desc
    | Options.SimpleStr desc -> [mk_field desc]
    | Options.EnumStr strs -> strs
    | Options.OpenEnumStr (strs, desc) -> strs @ [mk_field desc]
    | Options.PostProcessed (_, elem_spec)
    | Options.Accumulated elem_spec
    | Options.ReverseAccumulated elem_spec
    | Options.WithSideEffect (_, elem_spec) -> arg_snippets_of_type elem_spec in
  List.map (mk_snippet name) (arg_snippets_of_type typ)

let rec json_of_fstar_option_value = function
  | Options.Bool b -> JsonBool b
  | Options.String s
  | Options.Path s -> JsonStr s
  | Options.Int n -> JsonInt n
  | Options.List vs -> JsonList (List.map json_of_fstar_option_value vs)
  | Options.Unset -> JsonNull

let alist_of_fstar_option opt =
  [("name", JsonStr opt.opt_name);
   ("signature", JsonStr opt.opt_sig);
   ("value", json_of_fstar_option_value opt.opt_value);
   ("default", json_of_fstar_option_value opt.opt_default);
   ("documentation", json_of_opt JsonStr opt.opt_documentation);
   ("type", JsonStr (kind_of_fstar_option_type opt.opt_type));
   ("permission-level", JsonStr (string_of_option_permission_level opt.opt_permission_level))]

let json_of_fstar_option opt =
  JsonAssoc (alist_of_fstar_option opt)

let json_of_response qid status response =
  let qid = JsonStr qid in
  let status = match status with
               | QueryOK -> JsonStr "success"
               | QueryNOK -> JsonStr "failure"
               | QueryViolatesProtocol -> JsonStr "protocol-violation" in
  JsonAssoc [("kind", JsonStr "response");
             ("query-id", qid);
             ("status", status);
             ("response", response)]

let write_response qid status response =
  write_json (json_of_response qid status response)

let json_of_message level js_contents =
  JsonAssoc [("kind", JsonStr "message");
             ("query-id", json_of_opt JsonStr !repl_current_qid);
             ("level", JsonStr level);
             ("contents", js_contents)]

let forward_message callback level contents =
  callback (json_of_message level contents)

let json_of_hello =
  let js_version = JsonInt interactive_protocol_vernum in
  let js_features = JsonList (List.map JsonStr interactive_protocol_features) in
  JsonAssoc (("kind", JsonStr "protocol-info") :: alist_of_protocol_info)

let write_hello () =
  write_json json_of_hello

(*****************)
(* Options cache *)
(*****************)

let sig_of_fstar_option name typ =
  let flag = "--" ^ name in
  match Options.desc_of_opt_type typ with
  | None -> flag
  | Some arg_sig -> flag ^ " " ^ arg_sig

let fstar_options_list_cache =
  let defaults = SMap.of_list Options.defaults in
  Options.all_specs_with_types
  |> List.filter_map (fun (_shortname, name, typ, doc) ->
       SMap.try_find defaults name // Keep only options with a default value
       |> Util.map_option (fun default_value ->
             { opt_name = name;
               opt_sig = sig_of_fstar_option name typ;
               opt_value = Options.Unset;
               opt_default = default_value;
               opt_type = typ;
               opt_snippets = snippets_of_fstar_option name typ;
               opt_documentation = if doc = FStarC.Pprint.empty then None else Some (renderdoc doc);
               opt_permission_level = if Options.settable name then OptSet
                                      else OptReadOnly }))
  |> List.sortWith (fun o1 o2 ->
        String.compare (String.lowercase (o1.opt_name))
                       (String.lowercase (o2.opt_name)))

let fstar_options_map_cache =
  let cache = SMap.create 50 in
  List.iter (fun opt -> SMap.add cache opt.opt_name opt) fstar_options_list_cache;
  cache

let update_option opt =
  { opt with opt_value = Options.get_option opt.opt_name }

let current_fstar_options filter =
  List.map update_option (List.filter filter fstar_options_list_cache)

let trim_option_name opt_name =
  let opt_prefix = "--" in
  if Util.starts_with opt_name opt_prefix then
    (opt_prefix, Util.substring_from opt_name (String.length opt_prefix))
  else
    ("", opt_name)

(*************************)
(* Main interactive loop *)
(*************************)

let json_of_repl_state st =
  let filenames (_, (task, _)) =
    match task with
    | LDInterleaved (intf, impl) -> [intf.tf_fname; impl.tf_fname]
    | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
    | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
    | _ -> [] in

  JsonAssoc
    [("loaded-dependencies",
      JsonList (List.map JsonStr (List.concatMap filenames st.repl_deps_stack)));
     ("options",
      JsonList (List.map json_of_fstar_option (current_fstar_options (fun _ -> true))))]

let run_exit st =
  ((QueryOK, JsonNull), Inr 0)

let run_describe_protocol st =
  ((QueryOK, JsonAssoc alist_of_protocol_info), Inl st)

let run_describe_repl st =
  ((QueryOK, json_of_repl_state st), Inl st)

let run_protocol_violation st message =
  ((QueryViolatesProtocol, JsonStr message), Inl st)

let run_generic_error st message =
  ((QueryNOK, JsonStr message), Inl st)

let collect_errors () =
  let errors = FStarC.Errors.report_all() in
  FStarC.Errors.clear ();
  errors

let run_segment (st: repl_state) (code: string) =
  // Unfortunately, frag_fname is a special case in the interactive mode,
  // while in LSP, it is the only mode. To cope with this difference,
  // pass a frag_fname that is expected by the Interactive mode.
  let frag = { frag_fname = "<input>"; frag_text = code; frag_line = 1; frag_col = 0 } in

  let collect_decls () =
    match Parser.Driver.parse_fragment None frag with
    | Parser.Driver.Empty -> []
    | Parser.Driver.Decls decls
    | Parser.Driver.Modul (Parser.AST.Module {decls})
    | Parser.Driver.Modul (Parser.AST.Interface {decls}) -> decls in

  match with_captured_errors st.repl_env Util.sigint_ignore
            (fun _ -> Some <| collect_decls ()) with
    | None ->
      let errors = collect_errors () |> List.map json_of_issue in
      ((QueryNOK, JsonList errors), Inl st)
    | Some decls ->
      let json_of_decl decl =
        JsonAssoc [("def_range", json_of_def_range decl.Parser.AST.drange)] in
      let js_decls =
        JsonList <| List.map json_of_decl decls in
      ((QueryOK, JsonAssoc [("decls", js_decls)]), Inl st)

let run_vfs_add st opt_fname contents =
  let fname = Util.dflt st.repl_fname opt_fname in
  Parser.ParseIt.add_vfs_entry fname contents;
  ((QueryOK, JsonNull), Inl st)

let run_pop st =
  if nothing_left_to_pop st then
    ((QueryNOK, JsonStr "Too many pops"), Inl st)
  else
    let st' = pop_repl "pop_query" st in
    ((QueryOK, JsonNull), Inl st')

let write_progress stage contents_alist =
  let stage = match stage with Some s -> JsonStr s | None -> JsonNull in
  let js_contents = ("stage", stage) :: contents_alist in
  write_json (json_of_message "progress" (JsonAssoc js_contents))

let write_error contents =
  write_json (json_of_message "error" (JsonAssoc contents))

let write_repl_ld_task_progress task =
  match task with
  | LDInterleaved (_, tf) | LDSingle tf | LDInterfaceOfCurrentFile tf ->
    let modname = Parser.Dep.module_name_of_file tf.tf_fname in
    write_progress (Some "loading-dependency") [("modname", JsonStr modname)]
  | _ -> ()

(** Compute and load all dependencies of `filename`.

Return an new REPL state wrapped in ``Inr`` in case of failure, and a new REPL
plus with a list of completed tasks wrapped in ``Inl`` in case of success. **)
let load_deps st =
  match with_captured_errors st.repl_env Util.sigint_ignore
          (fun _env -> Some <| deps_and_repl_ld_tasks_of_our_file st.repl_fname) with
  | None -> Inr st
  | Some (deps, tasks, dep_graph) ->
    let st = {st with repl_env=FStarC.TypeChecker.Env.set_dep_graph st.repl_env dep_graph} in
    match run_repl_ld_transactions st tasks write_repl_ld_task_progress with
    | Inr st -> write_progress None []; Inr st
    | Inl st -> write_progress None []; Inl (st, deps)

let rephrase_dependency_error issue =
  { issue with issue_msg =
      let open FStarC.Pprint in
      (Errors.Msg.text "Error while computing or loading dependencies")::issue.issue_msg}

let write_full_buffer_fragment_progress (di:Incremental.fragment_progress) =
    let open FStarC.Interactive.Incremental in
    let json_of_code_fragment (cf:FStarC.Parser.ParseIt.code_fragment) =
        JsonAssoc ["range", json_of_def_range cf.range;
                   "code-digest", JsonStr (BU.digest_of_string cf.code)]
    in
    match di with
    | FullBufferStarted ->
      write_progress (Some "full-buffer-started") []
    
    | FragmentStarted d ->
      write_progress (Some "full-buffer-fragment-started")
                     ["ranges", json_of_def_range d.FStarC.Parser.AST.drange]
    | FragmentSuccess (d, cf, FullCheck) ->
      write_progress (Some "full-buffer-fragment-ok")
                     ["ranges", json_of_def_range d.FStarC.Parser.AST.drange;
                      "code-fragment", json_of_code_fragment cf]
    | FragmentSuccess (d, cf, LaxCheck) ->
      write_progress (Some "full-buffer-fragment-lax-ok")
                     ["ranges", json_of_def_range d.FStarC.Parser.AST.drange;
                      "code-fragment", json_of_code_fragment cf]
    | FragmentFailed d ->
      write_progress (Some "full-buffer-fragment-failed")
                     ["ranges", json_of_def_range d.FStarC.Parser.AST.drange]

    | FragmentError issues ->
      let qid =
        match !repl_current_qid with
        | None -> "unknown"
        | Some q -> q
      in
      write_json (json_of_response qid QueryNOK (JsonList (List.map json_of_issue issues)))

    | FullBufferFinished ->
      write_progress (Some "full-buffer-finished") []

let trunc_modul (m: SS.modul) (pred : SS.sigelt -> bool) : bool & SS.modul =
  let rec filter decls acc =
    match decls with
    | [] -> false, List.rev acc
    | d::ds ->
      if pred d then true, List.rev acc else filter ds (d::acc) in
  let found, decls = filter m.declarations [] in
  found, { m with SS.declarations = decls }

let load_partial_checked_file (env: TcEnv.env) (filename: string) (until_lid: string) =
  match FStarC.CheckedFiles.load_module_from_cache env filename with
  | None -> failwith ("cannot find checked file for " ^ filename)
  | Some tc_result ->
  let _, env = with_dsenv_of_tcenv env (fun ds -> (), DsEnv.set_current_module ds tc_result.checked_module.name) in
  let _, env = with_dsenv_of_tcenv env (fun ds -> (), DsEnv.set_iface_decls ds tc_result.checked_module.name []) in
  let pred se =
    let rec pred lids = match lids with
      | [] -> false
      | lid::lids -> if string_of_lid lid = until_lid then true else pred lids in
    pred (Syntax.Util.lids_of_sigelt se) in
  let found_decl, m = trunc_modul tc_result.checked_module pred in
  if not found_decl then failwith ("did not find declaration with lident " ^ until_lid) else
  let _, env = with_dsenv_of_tcenv env <|
      FStarC.ToSyntax.ToSyntax.add_partial_modul_to_env m tc_result.mii
        (FStarC.TypeChecker.Normalize.erase_universes env) in
  let env = FStarC.TypeChecker.Tc.load_partial_checked_module env m in
  let _, env = with_dsenv_of_tcenv env (fun ds -> (), DsEnv.set_current_module ds m.name) in
  let env = FStarC.TypeChecker.Env.set_current_module env m.name in
  ignore (FStarC.SMTEncoding.Encode.encode_modul env m);
  // TODO: opens / includes
  env, m

let run_load_partial_file st decl_name: (query_status & json) & either repl_state int =
  match load_deps st with
  | Inr st ->
    let errors = List.map rephrase_dependency_error (collect_errors ()) in
    let js_errors = errors |> List.map json_of_issue in
    ((QueryNOK, JsonList js_errors), Inl st)
  | Inl (st, deps) ->
    // We have to specify a push_kind here, otherwise push_repl will not snapshot the environment.
    let st = push_repl "load partial file" (Some FullCheck) Noop st in
    let env = st.repl_env in
    match with_captured_errors env Util.sigint_raise
              (fun env -> Some <| load_partial_checked_file env st.repl_fname decl_name) with
    | Some (env, curmod) when get_err_count () = 0 ->
      let st = { st with repl_curmod = Some curmod; repl_env = env } in
      ((QueryOK, JsonList []), Inl st)
    | _ ->
      let json_error_list = collect_errors () |> List.map json_of_issue in
      let json_errors = JsonList json_error_list in
      let st = pop_repl "load partial file" st in
      (QueryNOK, json_errors), Inl st

let run_push_without_deps st query
  : (query_status & json) & either repl_state int =
  let set_flychecking_flag st flag =
    { st with repl_env = { st.repl_env with flychecking = flag } } in

  let { push_code_or_decl = code_or_decl;
        push_line = line;
        push_column = column;
        push_peek_only = peek_only;
        push_kind = push_kind } = query in


  let _ =
    if FStarC.Options.ide_id_info_off()
    then TcEnv.toggle_id_info st.repl_env false
    else TcEnv.toggle_id_info st.repl_env true
  in
  let frag =
    match code_or_decl with
    | Inl text ->
      Inl { frag_fname = "<input>"; frag_text = text; frag_line = line; frag_col = column }
    | Inr (decl, _code) -> 
      Inr decl
    in
  let st = set_flychecking_flag st peek_only in
  let success, st = run_repl_transaction st (Some push_kind) peek_only (PushFragment (frag, push_kind, [])) in
  let st = set_flychecking_flag st false in

  let status = if success || peek_only then QueryOK else QueryNOK in
  let errs = collect_errors () in
  let has_error = 
      List.existsb 
        (fun i -> 
          match i.issue_level with
          | EError | ENotImplemented -> true
          | _ -> false)
        errs
  in
  let _ = 
    match code_or_decl with
    | Inr (d, s) ->
      if not has_error
      then write_full_buffer_fragment_progress (Incremental.FragmentSuccess (d, s, push_kind))
      else write_full_buffer_fragment_progress (Incremental.FragmentFailed d)
    | _ -> ()
  in
  let json_errors = JsonList (errs |> List.map json_of_issue) in
  let _ = 
    match errs, status with
    | _::_, QueryOK -> add_issues_to_push_fragment [json_errors]
    | _ -> ()
  in
  let st = if success then { st with repl_line = line; repl_column = column } else st in
  ((status, json_errors), Inl st)

let run_push_with_deps st query =
  if !dbg then
    Util.print_string "Reloading dependencies";
  TcEnv.toggle_id_info st.repl_env false;
  match load_deps st with
  | Inr st ->
    let errors = List.map rephrase_dependency_error (collect_errors ()) in
    let js_errors = errors |> List.map json_of_issue in
    ((QueryNOK, JsonList js_errors), Inl st)
  | Inl (st, deps) ->
    Options.restore_cmd_line_options false |> ignore;
    let names = add_module_completions st.repl_fname deps st.repl_names in
    run_push_without_deps ({ st with repl_names = names }) query

let run_push st query =
  if nothing_left_to_pop st then
    run_push_with_deps st query
  else
    run_push_without_deps st query

let run_symbol_lookup st symbol pos_opt requested_info (symbol_range_opt:option json) =
  match QH.symlookup st.repl_env symbol pos_opt requested_info with
  | None -> Inl "Symbol not found"
  | Some result ->
    Inr ("symbol", alist_of_symbol_lookup_result result symbol symbol_range_opt)

let run_option_lookup opt_name =
  let _, trimmed_name = trim_option_name opt_name in
  match SMap.try_find fstar_options_map_cache trimmed_name with
  | None -> Inl ("Unknown option:" ^ opt_name)
  | Some opt -> Inr ("option", alist_of_fstar_option (update_option opt))

let run_module_lookup st symbol =
  let query = Util.split symbol "." in
  match CTable.find_module_or_ns st.repl_names query with
  | None ->
    Inl "No such module or namespace"
  | Some (CTable.Module mod_info) ->
    Inr ("module", CTable.alist_of_mod_info mod_info)
  | Some (CTable.Namespace ns_info) ->
    Inr ("namespace", CTable.alist_of_ns_info ns_info)

let run_code_lookup st symbol pos_opt requested_info symrange_opt=
  match run_symbol_lookup st symbol pos_opt requested_info symrange_opt with
  | Inr alist -> Inr alist
  | Inl _ -> match run_module_lookup st symbol with
            | Inr alist -> Inr alist
            | Inl err_msg -> Inl "No such symbol, module, or namespace."

let run_lookup' st symbol context pos_opt requested_info symrange =
  match context with
  | LKSymbolOnly -> run_symbol_lookup st symbol pos_opt requested_info symrange
  | LKModule -> run_module_lookup st symbol
  | LKOption -> run_option_lookup symbol
  | LKCode -> run_code_lookup st symbol pos_opt requested_info symrange

let run_lookup st symbol context pos_opt requested_info symrange =
  try
    match run_lookup' st symbol context pos_opt requested_info symrange with
    | Inl err_msg -> (
      match symrange with
      | None ->
        //fstar-mode.el expects a failure on symbol not found
        ((QueryNOK, [JsonStr err_msg]), Inl st)
      | _ ->
        // This is the behavior for the vscode mode
        // No result found, but don't fail the query
         ((QueryOK, []), Inl st)
      )

    | Inr (kind, info) ->
      ((QueryOK, [JsonAssoc (("kind", JsonStr kind) :: info)]), Inl st)
  with
  | _ -> ((QueryOK, [JsonStr ("Lookup of " ^ symbol^ " failed")]), Inl st)


let run_code_autocomplete st search_term =
  let result = QH.ck_completion st search_term in
  let results = 
    match result with
    | [] -> result
    | _ ->
      let result_correlator : CTable.completion_result = {
        completion_match_length = 0;
        completion_annotation = "<search term>";
        completion_candidate = search_term
      } in
      result@[result_correlator]
  in
  let js = List.map CTable.json_of_completion_result results in
  ((QueryOK, JsonList js), Inl st)

let run_module_autocomplete st search_term modules namespaces =
  let needle = Util.split search_term "." in
  let mods_and_nss = CTable.autocomplete_mod_or_ns st.repl_names needle Some in
  let json = List.map CTable.json_of_completion_result mods_and_nss in
  ((QueryOK, JsonList json), Inl st)

let candidates_of_fstar_option match_len is_reset opt =
  let may_set, explanation =
    match opt.opt_permission_level with
    | OptSet -> true, ""
    | OptReadOnly -> false, "read-only" in
  let opt_type =
    kind_of_fstar_option_type opt.opt_type in
  let annot =
    if may_set then opt_type else "(" ^ explanation ^ " " ^ opt_type ^ ")" in
  opt.opt_snippets
  |> List.map (fun snippet ->
        { CTable.completion_match_length = match_len;
          CTable.completion_candidate = snippet;
          CTable.completion_annotation = annot })

let run_option_autocomplete st search_term is_reset =
  match trim_option_name search_term with
  | ("--", trimmed_name) ->
    let matcher opt = Util.starts_with opt.opt_name trimmed_name in
    let options = current_fstar_options matcher in

    let match_len = String.length search_term in
    let collect_candidates = candidates_of_fstar_option match_len is_reset in
    let results = List.concatMap collect_candidates options in

    let json = List.map CTable.json_of_completion_result results in
    ((QueryOK, JsonList json), Inl st)
  | (_, _) -> ((QueryNOK, JsonStr "Options should start with '--'"), Inl st)

let run_autocomplete st search_term context =
  match context with
  | CKCode ->
    run_code_autocomplete st search_term
  | CKOption is_reset ->
    run_option_autocomplete st search_term is_reset
  | CKModuleOrNamespace (modules, namespaces) ->
    run_module_autocomplete st search_term modules namespaces

let run_and_rewind st sigint_default task =
  let st = push_repl "run_and_rewind" (Some FullCheck) Noop st in
  let results =
    try Util.with_sigint_handler Util.sigint_raise (fun _ -> Inl <| task st)
    with | Util.SigInt -> Inl sigint_default
         | e -> Inr e in
  let st = pop_repl "run_and_rewind" st in
  match results with
  | Inl results -> (results, Inl st)
  | Inr e -> raise e // CPC fixme add a test with two computations

let run_with_parsed_and_tc_term st term line column continuation =
  let dummy_let_fragment term =
    let dummy_decl = Util.format1 "let __compute_dummy__ = (%s)" term in
    { frag_fname = " input"; frag_text = dummy_decl; frag_line = 0; frag_col = 0 } in

  let find_let_body ses =
    match ses with
    | [{ SS.sigel = SS.Sig_let {lbs=(_, [{ SS.lbunivs = univs; SS.lbdef = def }])} }] ->
      Some (univs, def)
    | _ -> None in

  let parse frag =
    match FStarC.Parser.ParseIt.parse None (FStarC.Parser.ParseIt.Incremental frag) with
    | FStarC.Parser.ParseIt.IncrementalFragment (decls, _, _err) -> Some (List.map fst decls)
    | _ -> None in

  let desugar env decls =
    fst (FStarC.ToSyntax.ToSyntax.decls_to_sigelts decls env.dsenv) in

  let typecheck tcenv decls =
    let ses, _ = FStarC.TypeChecker.Tc.tc_decls tcenv decls in
    ses in

  run_and_rewind st (QueryNOK, JsonStr "Computation interrupted") (fun st ->
    let tcenv = st.repl_env in
    let frag = dummy_let_fragment term in
    match parse frag with
    | None -> (QueryNOK, JsonStr "Could not parse this term")
    | Some decls ->
      let aux () =
        let decls = desugar tcenv decls in
        let ses = typecheck tcenv decls in
        match find_let_body ses with
        | None -> (QueryNOK, JsonStr "Typechecking yielded an unexpected term")
        | Some (univs, def) ->
          let univs, def = Syntax.Subst.open_univ_vars univs def in
          let tcenv = TcEnv.push_univ_vars tcenv univs in
          continuation tcenv def in
      if Options.trace_error () then
        aux ()
      else
        try aux ()
        with | e -> (match FStarC.Errors.issue_of_exn e with
                    | Some issue -> (QueryNOK, JsonStr (FStarC.Errors.format_issue issue))
                    | None -> raise e))

let run_compute st term rules =
  let rules =
    (match rules with
     | Some rules -> rules
     | None -> [FStarC.TypeChecker.Env.Beta;
               FStarC.TypeChecker.Env.Iota;
               FStarC.TypeChecker.Env.Zeta;
               FStarC.TypeChecker.Env.UnfoldUntil SS.delta_constant])
    @ [FStarC.TypeChecker.Env.Inlining;
       FStarC.TypeChecker.Env.Eager_unfolding;
       FStarC.TypeChecker.Env.DontUnfoldAttr [Parser.Const.tac_opaque_attr];
       FStarC.TypeChecker.Env.Primops] in

  let normalize_term tcenv rules t =
    FStarC.TypeChecker.Normalize.normalize rules tcenv t in

  run_with_parsed_and_tc_term st term 0 0 (fun tcenv def ->
      let normalized = normalize_term tcenv rules def in
      (QueryOK, JsonStr (term_to_string tcenv normalized)))

type search_term' =
| NameContainsStr of string
| TypeContainsLid of lid
and search_term = { st_negate: bool;
                    st_term: search_term' }

let st_cost = function
| NameContainsStr str -> - (String.length str)
| TypeContainsLid lid -> 1

type search_candidate = { sc_lid: lid; sc_typ:
                          ref (option Syntax.Syntax.typ);
                          sc_fvars: ref (option (RBSet.t lid)) }

let sc_of_lid lid = { sc_lid = lid;
                      sc_typ = mk_ref None;
                      sc_fvars = mk_ref None }

let sc_typ tcenv sc = // Memoized version of sc_typ
   match !sc.sc_typ with
   | Some t -> t
   | None -> let typ = match try_lookup_lid tcenv sc.sc_lid with
                       | None -> SS.mk SS.Tm_unknown Range.dummyRange
                       | Some ((_, typ), _) -> typ in
             sc.sc_typ := Some typ; typ

let sc_fvars tcenv sc = // Memoized version of fc_vars
   match !sc.sc_fvars with
   | Some fv -> fv
   | None -> let fv = Syntax.Free.fvars (sc_typ tcenv sc) in
             sc.sc_fvars := Some fv; fv

let json_of_search_result tcenv sc =
  let typ_str = term_to_string tcenv (sc_typ tcenv sc) in
  JsonAssoc [("lid", JsonStr (string_of_lid (DsEnv.shorten_lid tcenv.dsenv sc.sc_lid)));
             ("type", JsonStr typ_str)]

exception InvalidSearch of string

let run_search st search_str =
  let tcenv = st.repl_env in

  let st_matches candidate term =
    let found =
      match term.st_term with
      | NameContainsStr str -> Util.contains (string_of_lid candidate.sc_lid) str
      | TypeContainsLid lid -> Class.Setlike.mem lid (sc_fvars tcenv candidate) in
    found <> term.st_negate in

  let parse search_str =
    let parse_one term =
      let negate = Util.starts_with term "-" in
      let term = if negate then Util.substring_from term 1 else term in
      let beg_quote = Util.starts_with term "\"" in
      let end_quote = Util.ends_with term "\"" in
      let strip_quotes str =
        if String.length str < 2 then
          raise (InvalidSearch "Empty search term")
        else
          Util.substring str 1 (String.length term - 2) in
      let parsed =
        if beg_quote <> end_quote then
          raise (InvalidSearch (Util.format1 "Improperly quoted search term: %s" term))
        else if beg_quote then
          NameContainsStr (strip_quotes term)
        else
          let lid = Ident.lid_of_str term in
          match DsEnv.resolve_to_fully_qualified_name tcenv.dsenv lid with
          | None -> raise (InvalidSearch (Util.format1 "Unknown identifier: %s" term))
          | Some lid -> TypeContainsLid lid in
      { st_negate = negate; st_term = parsed } in

    let terms = List.map parse_one (Util.split search_str " ") in
    let cmp = fun x y -> st_cost x.st_term - st_cost y.st_term in
    Util.sort_with cmp terms in

  let pprint_one term =
    (if term.st_negate then "-" else "")
    ^ (match term.st_term with
       | NameContainsStr s -> Util.format1 "\"%s\"" s
       | TypeContainsLid l -> Util.format1 "%s" (string_of_lid l)) in

  let results =
    try
      let terms = parse search_str in
      let all_lidents = TcEnv.lidents tcenv in
      let all_candidates = List.map sc_of_lid all_lidents in
      let matches_all candidate = List.for_all (st_matches candidate) terms in
      let cmp r1 r2 = Util.compare (string_of_lid r1.sc_lid) (string_of_lid r2.sc_lid) in
      let results = List.filter matches_all all_candidates in
      let sorted = Util.sort_with cmp results in
      let js = List.map (json_of_search_result tcenv) sorted in
      match results with
      | [] -> let kwds = Util.concat_l " " (List.map pprint_one terms) in
              raise (InvalidSearch (Util.format1 "No results found for query [%s]" kwds))
      | _ -> (QueryOK, JsonList js)
    with InvalidSearch s -> (QueryNOK, JsonStr s) in
  (results, Inl st)

let run_format_code st code =
  let code_or_err = FStarC.Interactive.Incremental.format_code st code in
  match code_or_err with
  | Inl code -> 
    let result = JsonAssoc ["formatted-code", JsonStr code] in 
    (QueryOK, result), Inl st
  | Inr issue ->
    let result = JsonAssoc ["formatted-code-issue", JsonList (List.map json_of_issue issue)] in 
    (QueryNOK, result), Inl st

let as_json_list (q: (query_status & json) & either repl_state int)
  : (query_status & list json) & either repl_state int
  = let (q, j), s = q in
    (q, [j]), s

let run_query_result = (query_status & list json) & either repl_state int 

let maybe_cancel_queries st l = 
  let log_cancellation l = 
      if !dbg
      then List.iter (fun q -> BU.print1 "Cancelling query: %s\n" (query_to_string q)) l
  in
  match st.repl_buffered_input_queries with
  | { qq = Cancel p } :: rest -> (
    let st = { st with repl_buffered_input_queries = rest } in
    match p with
    | None -> //If no range, then cancel all remaining queries
      log_cancellation l;
      [], st
    | Some p -> //Cancel all queries that are within the range
      let query_ahead_of p q =
        let _, l, c = p in
        match q.qq with
        | Push pq -> pq.push_line >= l
        | _ -> false
      in
      let l = 
        match BU.prefix_until (query_ahead_of p) l with
        | None -> l
        | Some (l, q, qs) ->
          log_cancellation (q::qs);
          l
      in
      l, st
  )
  | _ -> l, st

let rec fold_query (f:repl_state -> query -> run_query_result)
                   (l:list query)
                   (st:repl_state)
  : run_query_result
  = match l with
    | [] -> (QueryOK, []), Inl st
    | q::l ->
      let (status, responses), st' = f st q in
      List.iter (write_response q.qid status) responses;
      match status, st' with
      | QueryOK, Inl st ->
        let st = buffer_input_queries st in
        let l, st = maybe_cancel_queries st l in
        fold_query f l st
      | _ ->
        (status, []), st'

let validate_query st (q: query) : query =
  match q.qq with
  | Push { push_kind = SyntaxCheck; push_peek_only = false } ->
    { qid = q.qid; qq = ProtocolViolation "Cannot use 'kind': 'syntax' with 'query': 'push'" }
  | _ -> match st.repl_curmod with
        | None when query_needs_current_module q.qq ->
          { qid = q.qid; qq = GenericError "Current module unset" }
        | _ -> q

let rec run_query st (q: query) : (query_status & list json) & either repl_state int =
  match q.qq with
  | Exit -> as_json_list (run_exit st)
  | DescribeProtocol -> as_json_list (run_describe_protocol st)
  | DescribeRepl -> as_json_list (run_describe_repl st)
  | GenericError message -> as_json_list (run_generic_error st message)
  | ProtocolViolation query -> as_json_list (run_protocol_violation st query)
  | Segment c -> as_json_list (run_segment st c)
  | VfsAdd (fname, contents) -> as_json_list (run_vfs_add st fname contents)
  | Push pquery -> as_json_list (run_push st pquery)
  | PushPartialCheckedFile decl_name -> as_json_list (run_load_partial_file st decl_name)
  | Pop -> as_json_list (run_pop st)
  | FullBuffer (code, full_kind, with_symbols) ->
    let open FStarC.Interactive.Incremental in
    write_full_buffer_fragment_progress FullBufferStarted;
    let queries, issues = 
      run_full_buffer st q.qid code full_kind with_symbols write_full_buffer_fragment_progress
    in
    List.iter (write_response q.qid QueryOK) issues;
    let res = fold_query validate_and_run_query queries st in
    write_full_buffer_fragment_progress FullBufferFinished;
    res
  | AutoComplete (search_term, context) ->
    as_json_list (run_autocomplete st search_term context)
  | Lookup (symbol, context, pos_opt, rq_info, symrange) ->
    run_lookup st symbol context pos_opt rq_info symrange
  | Compute (term, rules) ->
    as_json_list (run_compute st term rules)
  | Search term ->
    as_json_list (run_search st term)
  | Callback f ->
    f st
  | Format code ->
    as_json_list (run_format_code st code)
  | RestartSolver ->
    st.repl_env.solver.refresh None;
    (QueryOK, []), Inl st
  | Cancel _ ->
    //This should be handled in the fold_query loop above
    (QueryOK, []), Inl st
and validate_and_run_query st query =
  let query = validate_query st query in
  repl_current_qid := Some query.qid;
  if !dbg
  then BU.print2 "Running query %s: %s\n" query.qid (query_to_string query);
  run_query st query

(** This is the body of the JavaScript port's main loop. **)
let js_repl_eval st query =
  let (status, responses), st_opt = validate_and_run_query st query in
  let js_responses = List.map (json_of_response query.qid status) responses in
  js_responses, st_opt

let js_repl_eval_js st query_js =
  js_repl_eval st (deserialize_interactive_query query_js)

let js_repl_eval_str st query_str =
  let js_response, st_opt =
    js_repl_eval st (parse_interactive_query query_str) in
  (List.map string_of_json js_response), st_opt

(** This too is called from FStar.js **)
let js_repl_init_opts () =
  let res, fnames = Options.parse_cmd_line () in
  match res with
  | Getopt.Error (msg, _) -> failwith ("repl_init: " ^ msg)
  | Getopt.Help -> failwith "repl_init: --help unexpected"
  | Getopt.Success ->
    match fnames with
    | [] ->
      failwith "repl_init: No file name given in --ide invocation"
    | h :: _ :: _ ->
      failwith "repl_init: Too many file names given in --ide invocation"
    | _ -> ()

(** This is the main loop for the desktop version **)
let rec go st : int =
  let query, st = read_interactive_query st in
  let (status, responses), state_opt = validate_and_run_query st query in
  List.iter (write_response query.qid status) responses;
  match state_opt with
  | Inl st' -> go st'
  | Inr exitcode -> exitcode

let interactive_error_handler = // No printing here — collect everything for future use
  let issues : ref (list issue) = mk_ref [] in
  let add_one (e: issue) =
    let e = { e with issue_range = FStarC.Errors.fixup_issue_range e.issue_range } in
    issues := e :: !issues
  in
  let count_errors () =
    let issues = Util.remove_dups (fun i0 i1 -> i0=i1) !issues in
    List.length (List.filter (fun e -> e.issue_level = EError) issues)
  in
  let report () =
    List.sortWith compare_issues (Util.remove_dups (fun i0 i1 -> i0=i1) !issues)
  in
  let clear () = issues := [] in
  { eh_name = "interactive error handler";
    eh_add_one = add_one;
    eh_count_errors = count_errors;
    eh_report = report;
    eh_clear = clear }

let interactive_printer printer =
  { printer_prinfo = (fun s -> forward_message printer "info" (JsonStr s));
    printer_prwarning = (fun s -> forward_message printer "warning" (JsonStr s));
    printer_prerror = (fun s -> forward_message printer "error" (JsonStr s));
    printer_prgeneric = (fun label get_string get_json ->
                         forward_message printer label (get_json ())) }

let install_ide_mode_hooks printer =
  FStarC.Util.set_printer (interactive_printer printer);
  FStarC.Errors.set_handler interactive_error_handler


let build_initial_repl_state (filename: string) =
  let env = init_env FStarC.Parser.Dep.empty_deps in
  let env = FStarC.TypeChecker.Env.set_range env initial_range in
  FStarC.Options.set_ide_filename filename;
  { repl_line = 1;
    repl_column = 0;
    repl_fname = filename;
    repl_curmod = None;
    repl_env = env;
    repl_deps_stack = [];
    repl_stdin = open_stdin ();
    repl_names = CompletionTable.empty;
    repl_buffered_input_queries = [];
    repl_lang = [] }

let interactive_mode' init_st =
  write_hello ();

  let exit_code =
    let fn = List.hd (Options.file_list ()) in
    SMTEncoding.Solver.with_hints_db fn (fun () -> go init_st)
  in
  exit exit_code

let interactive_mode (filename:string): unit =
  install_ide_mode_hooks write_json;
  // Ignore unexpected interrupts (some methods override this handler)
  Util.set_sigint_handler Util.sigint_ignore;

  if Option.isSome (Options.codegen ()) then
    Errors.log_issue0 Errors.Warning_IDEIgnoreCodeGen "--ide: ignoring --codegen";

  let init = build_initial_repl_state filename in
  if Options.trace_error () then
    // This prevents the error catcher below from swallowing backtraces
    interactive_mode' init
  else
    try
      interactive_mode' init
    with
    | e -> (// Revert to default handler since we won't have an opportunity to
           // print errors ourselves.
           FStarC.Errors.set_handler FStarC.Errors.default_handler;
           raise e)
