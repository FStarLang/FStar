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
#light "off"

module FStar.Interactive.Ide
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.Range
open FStar.Util
open FStar.Getopt
open FStar.Ident
open FStar.Errors
open FStar.JsonHelper
open FStar.QueryHelper
open FStar.PushHelper

open FStar.Universal
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common
open FStar.Interactive
open FStar.Parser.ParseIt

module SS = FStar.Syntax.Syntax
module DsEnv = FStar.Syntax.DsEnv
module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable
module QH = FStar.QueryHelper

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
    Errors.log_issue (TcEnv.get_range env) (Errors.Error_IDEAssertionFailure, msg);
    None

  | Util.SigInt ->
    Util.print_string "Interrupted"; None

  | Error (e, msg, r) ->
    Errors.add_errors [(e, msg, r)];
    None

  | Err (e, msg) ->
    Errors.add_errors [(e, msg, TcEnv.get_range env)];
    None

  | Stop ->
    None

let with_captured_errors env sigint_handler f =
  if Options.trace_error () then f env
  else with_captured_errors' env sigint_handler f

(*************************)
(* REPL tasks and states *)
(*************************)

let t0 = Util.now ()

(** Create a timed_fname with a dummy modtime **)
let dummy_tf_of_fname fname =
  { tf_fname = fname;
    tf_modtime = t0 }

let string_of_timed_fname { tf_fname = fname; tf_modtime = modtime } =
  if modtime = t0 then Util.format1 "{ %s }" fname
  else Util.format2 "{ %s; %s }" fname (string_of_time modtime)

type push_query =
  { push_kind: push_kind;
    push_code: string;
    push_line: int; push_column: int;
    push_peek_only: bool }

(** Tasks describing each snapshot of the REPL state. **)

type env_t = TcEnv.env

let repl_current_qid : ref<option<string>> = Util.mk_ref None // For messages

(** Check whether users can issue further ``pop`` commands. **)
let nothing_left_to_pop st =
  (* The first ``length st.repl_deps_stack`` entries in ``repl_stack`` are
     dependency-loading entries, which the user may not pop (since they didn't
     push them). *)
  List.length !repl_stack = List.length st.repl_deps_stack

(*********************)
(* Dependency checks *)
(*********************)

let string_of_repl_task = function
  | LDInterleaved (intf, impl) ->
    Util.format2 "LDInterleaved (%s, %s)" (string_of_timed_fname intf) (string_of_timed_fname impl)
  | LDSingle intf_or_impl ->
    Util.format1 "LDSingle %s" (string_of_timed_fname intf_or_impl)
  | LDInterfaceOfCurrentFile intf ->
    Util.format1 "LDInterfaceOfCurrentFile %s" (string_of_timed_fname intf)
  | PushFragment frag ->
    Util.format1 "PushFragment { code = %s }" frag.frag_text
  | Noop -> "Noop {}"

(** Push, run `task`, and pop if it fails.

If `must_rollback` is set, always pop.  Returns a pair: a boolean indicating
success, and a new REPL state. **)
let run_repl_transaction st push_kind must_rollback task =
  let st = push_repl "run_repl_transaction" push_kind task st in
  let env, finish_name_tracking = track_name_changes st.repl_env in // begin name tracking…

  let check_success () =
    get_err_count () = 0 && not must_rollback in

  // Run the task (and capture errors)
  let curmod, env, success =
    match with_captured_errors env Util.sigint_raise
              (fun env -> Some <| run_repl_task st.repl_curmod env task) with
    | Some (curmod, env) when check_success () -> curmod, env, true
    | _ -> st.repl_curmod, env, false in

  let env, name_events = finish_name_tracking env in // …end name tracking
  let st =
    if success then
      let st = { st with repl_env = env; repl_curmod = curmod } in
      commit_name_tracking st name_events
    else
      pop_repl "run_repl_transaction" st in

  (success, st)

(** Load dependencies described by `tasks`.

Returns a new REPL state, wrapped in ``Inl`` to indicate complete success or
``Inr`` to indicate a partial failure.  That new state has an updated
``repl_deps_stack``, containing loaded dependencies in reverse order compared to
the original list of tasks: the first dependencies (prims, …) come first; the
current file's interface comes last.

The original value of the ``repl_deps_stack`` field in ``st`` is used to skip
already completed tasks.

This function is stateful: it uses ``push_repl`` and ``pop_repl``.

`progress_callback` is called once per task, right before the task is run. **)
let run_repl_ld_transactions (st: repl_state) (tasks: list<repl_task>)
                             (progress_callback: repl_task -> unit) =
  let debug verb task =
    if Options.debug_any () then
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
      let dep_graph = FStar.TypeChecker.Env.dep_graph st.repl_env in
      let st' = {st' with repl_env=FStar.TypeChecker.Env.set_dep_graph st'.repl_env dep_graph} in
      revert_many st' entries in

  let rec aux (st: repl_state)
              (tasks: list<repl_task>)
              (previous: list<repl_stack_entry_t>) =
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
      let success, st = run_repl_transaction st push_kind false timestamped_task in
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

(*****************************************)
(* Reading queries and writing responses *)
(*****************************************)

let js_pushkind s : push_kind = match js_str s with
  | "syntax" -> SyntaxCheck
  | "lax" -> LaxCheck
  | "full" -> FullCheck
  | _ -> js_fail "push_kind" s

let js_reductionrule s = match js_str s with
  | "beta" -> FStar.TypeChecker.Env.Beta
  | "delta" -> FStar.TypeChecker.Env.UnfoldUntil SS.delta_constant
  | "iota" -> FStar.TypeChecker.Env.Iota
  | "zeta" -> FStar.TypeChecker.Env.Zeta
  | "reify" -> FStar.TypeChecker.Env.Reify
  | "pure-subterms" -> FStar.TypeChecker.Env.PureSubtermsWithinComputations
  | _ -> js_fail "reduction rule" s

type completion_context =
| CKCode
| CKOption of bool (* #set-options (false) or #reset-options (true) *)
| CKModuleOrNamespace of bool (* modules *) * bool (* namespaces *)

let js_optional_completion_context k =
  match k with
  | None -> CKCode
  | Some k ->
    match js_str k with
    | "symbol" // Backwards compatibility
    | "code" -> CKCode
    | "set-options" -> CKOption false
    | "reset-options" -> CKOption true
    | "open"
    | "let-open" -> CKModuleOrNamespace (true, true)
    | "include"
    | "module-alias" -> CKModuleOrNamespace (true, false)
    | _ ->
      js_fail "completion context (code, set-options, reset-options, \
open, let-open, include, module-alias)" k

type lookup_context =
| LKSymbolOnly
| LKModule
| LKOption
| LKCode

let js_optional_lookup_context k =
  match k with
  | None -> LKSymbolOnly // Backwards-compatible default
  | Some k ->
    match js_str k with
    | "symbol-only" -> LKSymbolOnly
    | "code" -> LKCode
    | "set-options"
    | "reset-options" -> LKOption
    | "open"
    | "let-open"
    | "include"
    | "module-alias" -> LKModule
    | _ ->
      js_fail "lookup context (symbol-only, code, set-options, reset-options, \
open, let-open, include, module-alias)" k

type position = string * int * int

type query' =
| Exit
| DescribeProtocol
| DescribeRepl
| Segment of string (* File contents *)
| Pop
| Push of push_query
| VfsAdd of option<string> (* fname *) * string (* contents *)
| AutoComplete of string * completion_context
| Lookup of string * lookup_context * option<position> * list<string>
| Compute of string * option<list<FStar.TypeChecker.Env.step>>
| Search of string
| GenericError of string
| ProtocolViolation of string
and query = { qq: query'; qid: string }

let query_needs_current_module = function
  | Exit | DescribeProtocol | DescribeRepl | Segment _
  | Pop | Push { push_peek_only = false } | VfsAdd _
  | GenericError _ | ProtocolViolation _ -> false
  | Push _ | AutoComplete _ | Lookup _ | Compute _ | Search _ -> true

let interactive_protocol_vernum = 2

let interactive_protocol_features =
  ["autocomplete"; "autocomplete/context";
   "compute"; "compute/reify"; "compute/pure-subterms";
   "describe-protocol"; "describe-repl"; "exit";
   "lookup"; "lookup/context"; "lookup/documentation"; "lookup/definition";
   "peek"; "pop"; "push"; "search"; "segment";
   "vfs-add"; "tactic-ranges"; "interrupt"; "progress"]

type query_status = | QueryOK | QueryNOK | QueryViolatesProtocol

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

    { qid = qid;
      qq = match query with
           | "exit" -> Exit
           | "pop" -> Pop
           | "describe-protocol" -> DescribeProtocol
           | "describe-repl" -> DescribeRepl
           | "segment" -> Segment (arg "code" |> js_str)
           | "peek" | "push" -> Push ({ push_kind = arg "kind" |> js_pushkind;
                                       push_code = arg "code" |> js_str;
                                       push_line = arg "line" |> js_int;
                                       push_column = arg "column" |> js_int;
                                       push_peek_only = query = "peek" })
           | "autocomplete" -> AutoComplete (arg "partial-symbol" |> js_str,
                                            try_arg "context" |> js_optional_completion_context)
           | "lookup" -> Lookup (arg "symbol" |> js_str,
                                try_arg "context" |> js_optional_lookup_context,
                                try_arg "location"
                                  |> Util.map_option js_assoc
                                  |> Util.map_option (fun loc ->
                                      (assoc "[location]" "filename" loc |> js_str,
                                       assoc "[location]" "line" loc |> js_int,
                                       assoc "[location]" "column" loc |> js_int)),
                                arg "requested-info" |> js_list js_str)
           | "compute" -> Compute (arg "term" |> js_str,
                                  try_arg "rules"
                                    |> Util.map_option (js_list js_reductionrule))
           | "search" -> Search (arg "terms" |> js_str)
           | "vfs-add" -> VfsAdd (try_arg "filename" |> Util.map_option js_str,
                                 arg "contents" |> js_str)
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
  match Util.json_of_string query_str with
  | None -> { qid = "?"; qq = ProtocolViolation "Json parsing failed." }
  | Some request -> deserialize_interactive_query request

let read_interactive_query stream : query =
  match Util.read_line stream with
  | None -> exit 0
  | Some line -> parse_interactive_query line

let json_of_opt json_of_a opt_a =
  Util.dflt JsonNull (Util.map_option json_of_a opt_a)

let json_of_issue_level i =
  JsonStr (match i with
           | ENotImplemented -> "not-implemented"
           | EInfo -> "info"
           | EWarning -> "warning"
           | EError -> "error")

let json_of_issue issue =
  JsonAssoc [("level", json_of_issue_level issue.issue_level);
             ("message", JsonStr issue.issue_message);
             ("ranges", JsonList
                          ((match issue.issue_range with
                            | None -> []
                            | Some r -> [json_of_use_range r]) @
                           (match issue.issue_range with
                            | Some r when def_range r <> use_range r ->
                              [json_of_def_range r]
                            | _ -> [])))]

let alist_of_symbol_lookup_result lr =
  [("name", JsonStr lr.slr_name);
   ("defined-at", json_of_opt json_of_def_range lr.slr_def_range);
   ("type", json_of_opt JsonStr lr.slr_typ);
   ("documentation", json_of_opt JsonStr lr.slr_doc);
   ("definition", json_of_opt JsonStr lr.slr_def)]

let alist_of_protocol_info =
  let js_version = JsonInt interactive_protocol_vernum in
  let js_features = JsonList <| List.map JsonStr interactive_protocol_features in
  [("version", js_version); ("features", js_features)]

type fstar_option_permission_level =
| OptSet
| OptReset
| OptReadOnly

let string_of_option_permission_level = function
  | OptSet -> ""
  | OptReset -> "requires #reset-options"
  | OptReadOnly -> "read-only"

type fstar_option =
  { opt_name: string;
    opt_sig: string;
    opt_value: Options.option_val;
    opt_default: Options.option_val;
    opt_type: Options.opt_type;
    opt_snippets: list<string>;
    opt_documentation: option<string>;
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

let rec snippets_of_fstar_option name typ =
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
  let defaults = Util.smap_of_list Options.defaults in
  Options.all_specs_with_types
  |> List.filter_map (fun (_shortname, name, typ, doc) ->
       Util.smap_try_find defaults name // Keep only options with a default value
       |> Util.map_option (fun default_value ->
             { opt_name = name;
               opt_sig = sig_of_fstar_option name typ;
               opt_value = Options.Unset;
               opt_default = default_value;
               opt_type = typ;
               opt_snippets = snippets_of_fstar_option name typ;
               opt_documentation = if doc = "" then None else Some doc;
               opt_permission_level = if Options.settable name then OptSet
                                      else if Options.resettable name then OptReset
                                      else OptReadOnly }))
  |> List.sortWith (fun o1 o2 ->
        String.compare (String.lowercase (o1.opt_name))
                       (String.lowercase (o2.opt_name)))

let fstar_options_map_cache =
  let cache = Util.smap_create 50 in
  List.iter (fun opt -> Util.smap_add cache opt.opt_name opt) fstar_options_list_cache;
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
  let errors = FStar.Errors.report_all() in
  FStar.Errors.clear ();
  errors

let run_segment (st: repl_state) (code: string) =
  let frag = { frag_fname = "<input>"; frag_text = code; frag_line = 1; frag_col = 0 } in

  let collect_decls () =
    match Parser.Driver.parse_fragment frag with
    | Parser.Driver.Empty -> []
    | Parser.Driver.Decls decls
    | Parser.Driver.Modul (Parser.AST.Module (_, decls))
    | Parser.Driver.Modul (Parser.AST.Interface (_, decls, _)) -> decls in

  match with_captured_errors st.repl_env Util.sigint_ignore
            (fun _ -> Some <| collect_decls ()) with
    | None ->
      let errors = collect_errors () |> List.map json_of_issue in
      ((QueryNOK, JsonList errors), Inl st)
    | Some decls ->
      let json_of_decl decl =
        JsonAssoc [("def_range", json_of_def_range (Parser.AST.decl_drange decl))] in
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
    let st = {st with repl_env=FStar.TypeChecker.Env.set_dep_graph st.repl_env dep_graph} in
    match run_repl_ld_transactions st tasks write_repl_ld_task_progress with
    | Inr st -> write_progress None []; Inr st
    | Inl st -> write_progress None []; Inl (st, deps)

let rephrase_dependency_error issue =
  { issue with issue_message =
               format1 "Error while computing or loading dependencies:\n%s"
                       issue.issue_message }

let run_push_without_deps st query =
  let set_nosynth_flag st flag =
    { st with repl_env = { st.repl_env with nosynth = flag } } in

  let { push_code = text; push_line = line; push_column = column;
        push_peek_only = peek_only; push_kind = push_kind } = query in

  let frag = { frag_fname = "<input>"; frag_text = text; frag_line = line; frag_col = column } in

  TcEnv.toggle_id_info st.repl_env true;
  let st = set_nosynth_flag st peek_only in
  let success, st = run_repl_transaction st push_kind peek_only (PushFragment frag) in
  let st = set_nosynth_flag st false in

  let status = if success || peek_only then QueryOK else QueryNOK in
  let json_errors = JsonList (collect_errors () |> List.map json_of_issue) in
  let st = if success then { st with repl_line = line; repl_column = column } else st in
  ((status, json_errors), Inl st)

let run_push_with_deps st query =
  if Options.debug_any () then
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

let run_symbol_lookup st symbol pos_opt requested_info =
  match QH.symlookup st.repl_env symbol pos_opt requested_info with
  | None -> Inl "Symbol not found"
  | Some result -> Inr ("symbol", alist_of_symbol_lookup_result result)

let run_option_lookup opt_name =
  let _, trimmed_name = trim_option_name opt_name in
  match Util.smap_try_find fstar_options_map_cache trimmed_name with
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

let run_code_lookup st symbol pos_opt requested_info =
  match run_symbol_lookup st symbol pos_opt requested_info with
  | Inr alist -> Inr alist
  | Inl _ -> match run_module_lookup st symbol with
            | Inr alist -> Inr alist
            | Inl err_msg -> Inl "No such symbol, module, or namespace."

let run_lookup' st symbol context pos_opt requested_info =
  match context with
  | LKSymbolOnly -> run_symbol_lookup st symbol pos_opt requested_info
  | LKModule -> run_module_lookup st symbol
  | LKOption -> run_option_lookup symbol
  | LKCode -> run_code_lookup st symbol pos_opt requested_info

let run_lookup st symbol context pos_opt requested_info =
  match run_lookup' st symbol context pos_opt requested_info with
  | Inl err_msg ->
    ((QueryNOK, JsonStr err_msg), Inl st)
  | Inr (kind, info) ->
    ((QueryOK, JsonAssoc (("kind", JsonStr kind) :: info)), Inl st)

let run_code_autocomplete st search_term =
  let result = QH.ck_completion st search_term in
  let js = List.map CTable.json_of_completion_result result in
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
    | OptReset -> is_reset, "#reset-only"
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
  let st = push_repl "run_and_rewind" FullCheck Noop st in
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
    { frag_fname = "<input>"; frag_text = dummy_decl; frag_line = 0; frag_col = 0 } in

  let find_let_body ses =
    match ses with
    | [{ SS.sigel = SS.Sig_let((_, [{ SS.lbunivs = univs; SS.lbdef = def }]), _) }] ->
      Some (univs, def)
    | _ -> None in

  let parse frag =
    match FStar.Parser.ParseIt.parse (FStar.Parser.ParseIt.Toplevel frag) with
    | FStar.Parser.ParseIt.ASTFragment (Inr decls, _) -> Some decls
    | _ -> None in

  let desugar env decls =
    fst (FStar.ToSyntax.ToSyntax.decls_to_sigelts decls env.dsenv) in

  let typecheck tcenv decls =
    let ses, _, _ = FStar.TypeChecker.Tc.tc_decls tcenv decls in
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
        with | e -> (match FStar.Errors.issue_of_exn e with
                    | Some issue -> (QueryNOK, JsonStr (FStar.Errors.format_issue issue))
                    | None -> raise e))

let run_compute st term rules =
  let rules =
    (match rules with
     | Some rules -> rules
     | None -> [FStar.TypeChecker.Env.Beta;
               FStar.TypeChecker.Env.Iota;
               FStar.TypeChecker.Env.Zeta;
               FStar.TypeChecker.Env.UnfoldUntil SS.delta_constant])
    @ [FStar.TypeChecker.Env.Inlining;
       FStar.TypeChecker.Env.Eager_unfolding;
       FStar.TypeChecker.Env.UnfoldTac;
       FStar.TypeChecker.Env.Primops] in

  let normalize_term tcenv rules t =
    FStar.TypeChecker.Normalize.normalize rules tcenv t in

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
                          ref<option<Syntax.Syntax.typ>>;
                          sc_fvars: ref<option<set<lid>>> }

let sc_of_lid lid = { sc_lid = lid;
                      sc_typ = Util.mk_ref None;
                      sc_fvars = Util.mk_ref None }

let sc_typ tcenv sc = // Memoized version of sc_typ
   match !sc.sc_typ with
   | Some t -> t
   | None -> let typ = match try_lookup_lid tcenv sc.sc_lid with
                       | None -> SS.mk SS.Tm_unknown None Range.dummyRange
                       | Some ((_, typ), _) -> typ in
             sc.sc_typ := Some typ; typ

let sc_fvars tcenv sc = // Memoized version of fc_vars
   match !sc.sc_fvars with
   | Some fv -> fv
   | None -> let fv = Syntax.Free.fvars (sc_typ tcenv sc) in
             sc.sc_fvars := Some fv; fv

let json_of_search_result tcenv sc =
  let typ_str = term_to_string tcenv (sc_typ tcenv sc) in
  JsonAssoc [("lid", JsonStr (DsEnv.shorten_lid tcenv.dsenv sc.sc_lid).str);
             ("type", JsonStr typ_str)]

exception InvalidSearch of string

let run_search st search_str =
  let tcenv = st.repl_env in
  let empty_fv_set = SS.new_fv_set () in

  let st_matches candidate term =
    let found =
      match term.st_term with
      | NameContainsStr str -> Util.contains candidate.sc_lid.str str
      | TypeContainsLid lid -> set_mem lid (sc_fvars tcenv candidate) in
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
       | TypeContainsLid l -> Util.format1 "%s" l.str) in

  let results =
    try
      let terms = parse search_str in
      let all_lidents = TcEnv.lidents tcenv in
      let all_candidates = List.map sc_of_lid all_lidents in
      let matches_all candidate = List.for_all (st_matches candidate) terms in
      let cmp r1 r2 = Util.compare r1.sc_lid.str r2.sc_lid.str in
      let results = List.filter matches_all all_candidates in
      let sorted = Util.sort_with cmp results in
      let js = List.map (json_of_search_result tcenv) sorted in
      match results with
      | [] -> let kwds = Util.concat_l " " (List.map pprint_one terms) in
              raise (InvalidSearch (Util.format1 "No results found for query [%s]" kwds))
      | _ -> (QueryOK, JsonList js)
    with InvalidSearch s -> (QueryNOK, JsonStr s) in
  (results, Inl st)

let run_query st (q: query') : (query_status * json) * either<repl_state, int> =
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
  | AutoComplete (search_term, context) -> run_autocomplete st search_term context
  | Lookup (symbol, context, pos_opt, rq_info) -> run_lookup st symbol context pos_opt rq_info
  | Compute (term, rules) -> run_compute st term rules
  | Search term -> run_search st term

let validate_query st (q: query) : query =
  match q.qq with
  | Push { push_kind = SyntaxCheck; push_peek_only = false } ->
    { qid = q.qid; qq = ProtocolViolation "Cannot use 'kind': 'syntax' with 'query': 'push'" }
  | _ -> match st.repl_curmod with
        | None when query_needs_current_module q.qq ->
          { qid = q.qid; qq = GenericError "Current module unset" }
        | _ -> q

let validate_and_run_query st query =
  let query = validate_query st query in
  repl_current_qid := Some query.qid;
  run_query st query.qq

(** This is the body of the JavaScript port's main loop. **)
let js_repl_eval st query =
  let (status, response), st_opt = validate_and_run_query st query in
  let js_response = json_of_response query.qid status response in
  js_response, st_opt

let js_repl_eval_js st query_js =
  js_repl_eval st (deserialize_interactive_query query_js)

let js_repl_eval_str st query_str =
  let js_response, st_opt =
    js_repl_eval st (parse_interactive_query query_str) in
  (Util.string_of_json js_response), st_opt

(** This too is called from FStar.js **)
let js_repl_init_opts () =
  let res, fnames = Options.parse_cmd_line () in
  match res with
  | Getopt.Error msg -> failwith ("repl_init: " ^ msg)
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
  let query = read_interactive_query st.repl_stdin in
  let (status, response), state_opt = validate_and_run_query st query in
  write_response query.qid status response;
  match state_opt with
  | Inl st' -> go st'
  | Inr exitcode -> exitcode

let interactive_error_handler = // No printing here — collect everything for future use
  let issues : ref<list<issue>> = Util.mk_ref [] in
  let add_one (e: issue) = issues := e :: !issues in
  let count_errors () = List.length (List.filter (fun e -> e.issue_level = EError) !issues) in
  let report () = List.sortWith compare_issues !issues in
  let clear () = issues := [] in
  { eh_add_one = add_one;
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
  FStar.Util.set_printer (interactive_printer printer);
  FStar.Errors.set_handler interactive_error_handler

let initial_range fname =
  Range.mk_range fname (Range.mk_pos 1 0) (Range.mk_pos 1 0)

let build_initial_repl_state (filename: string) =
  let env = init_env FStar.Parser.Dep.empty_deps in
  let env = FStar.TypeChecker.Env.set_range env (initial_range filename) in

  { repl_line = 1; repl_column = 0; repl_fname = filename;
    repl_curmod = None; repl_env = env; repl_deps_stack = [];
    repl_stdin = open_stdin ();
    repl_names = CompletionTable.empty }

let interactive_mode' init_st =
  write_hello ();

  let exit_code =
    if FStar.Options.record_hints() || FStar.Options.use_hints() then
      FStar.SMTEncoding.Solver.with_hints_db (List.hd (Options.file_list ())) (fun () -> go init_st)
    else
      go init_st in
  exit exit_code

let interactive_mode (filename:string): unit =
  install_ide_mode_hooks write_json;

  // Ignore unexpected interrupts (some methods override this handler)
  Util.set_sigint_handler Util.sigint_ignore;

  if Option.isSome (Options.codegen ()) then
    Errors.log_issue Range.dummyRange (Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen");

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
           FStar.Errors.set_handler FStar.Errors.default_handler;
           raise e)
