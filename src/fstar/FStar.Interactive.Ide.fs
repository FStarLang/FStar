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

open FStar.Universal
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common
open FStar.Interactive
open FStar.Parser.ParseIt

module SS = FStar.Syntax.Syntax
module DsEnv = FStar.ToSyntax.Env
module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable

exception ExitREPL of int

let push env msg =
  let res = push_context env msg in
  Options.push();
  res

let pop env msg =
  pop_context env msg;
  Options.pop()

type push_kind = | SyntaxCheck | LaxCheck | FullCheck

let set_check_kind env check_kind =
  { env with lax = (check_kind = LaxCheck);
             dsenv = DsEnv.set_syntax_only env.dsenv (check_kind = SyntaxCheck)}

let with_captured_errors' env f =
  try
    f env
  with
  | Failure (msg) ->
    let msg = "ASSERTION FAILURE: " ^ msg ^ "\n" ^
              "F* may be in an inconsistent state.\n" ^
              "Please file a bug report, ideally with a " ^
              "minimized version of the program that triggered the error." in
    TcErr.add_errors env [(msg, TcEnv.get_range env)];
    // Make sure the user sees the error, even if it happened transiently while
    // running an automatic syntax checker like FlyCheck.
    Util.print_error msg;
    None

  | Error(msg, r) ->
    TcErr.add_errors env [(msg, r)];
    None

  | Err msg ->
    TcErr.add_errors env [(msg, TcEnv.get_range env)];
    None

let with_captured_errors env f =
  if Options.trace_error () then f env
  else with_captured_errors' env f

(*************************)
(* REPL tasks and states *)
(*************************)

type timed_fname =
  { tf_fname: string;
    tf_modtime: time }

let t0 = Util.now ()

let tf_of_fname fname =
  { tf_fname = fname;
    tf_modtime = Parser.ParseIt.get_file_last_modification_time fname }

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

type optmod_t = option<Syntax.Syntax.modul>

(** Tasks describing each snapshot of the REPL state.

Every snapshot pushed in the repl stack is annotated with one of these.  The
``LD``-prefixed (“Load Dependency”) onces are useful when loading or updating
dependencies, as they carry enough information to determine whether a dependency
is stale. **)
type repl_task =
  | LDInterleaved of timed_fname * timed_fname (* (interface * implementation) *)
  | LDSingle of timed_fname (* interface or implementation *)
  | LDInterfaceOfCurrentFile of timed_fname (* interface *)
  | PushFragment of input_frag (* code fragment *)

type env_t = TcEnv.env

type repl_state = { repl_line: int; repl_column: int; repl_fname: string;
                    repl_deps_stack: repl_stack_t;
                    repl_curmod: optmod_t;
                    repl_env: env_t;
                    repl_stdin: stream_reader;
                    repl_names: CTable.table }
and repl_stack_t = list<completed_repl_task>
and completed_repl_task = repl_task * repl_state

let repl_stack: ref<repl_stack_t> = Util.mk_ref []

let pop_repl st =
  match !repl_stack with
  | [] -> failwith "Too many pops"
  | (_, st') :: stack ->
    pop st.repl_env "#pop";
    repl_stack := stack;
    st'

let push_repl push_kind task st =
  repl_stack := (task, st) :: !repl_stack;
  push (set_check_kind st.repl_env push_kind) ""

(** Check whether users can issue further ``pop`` commands. **)
let nothing_left_to_pop st =
  (* The first ``length st.repl_deps_stack`` entries in ``repl_stack`` are
     dependency-loading entries, which the user may not pop (since they didn't
     push them). *)
  List.length !repl_stack = List.length st.repl_deps_stack

(*****************)
(* Name tracking *)
(*****************)

type name_tracking_event =
| NTAlias of lid (* host *) * ident (* alias *) * lid (* aliased *)
| NTOpen of lid (* host *) * DsEnv.open_module_or_namespace (* opened *)
| NTInclude of lid (* host *) * lid (* included *)
| NTBinding of binding

let query_of_ids (ids: list<ident>) : CTable.query =
  List.map text_of_id ids

let query_of_lid (lid: lident) : CTable.query =
  query_of_ids (lid.ns @ [lid.ident])

let update_names_from_event cur_mod_str table evt =
  let is_cur_mod lid = lid.str = cur_mod_str in
  match evt with
  | NTAlias (host, id, included) ->
    if is_cur_mod host then
      CTable.register_alias
        table (text_of_id id) [] (query_of_lid included)
    else
      table
  | NTOpen (host, (included, kind)) ->
    if is_cur_mod host then
      CTable.register_open
        table (kind = DsEnv.Open_module) [] (query_of_lid included)
    else
      table
  | NTInclude (host, included) ->
    CTable.register_include
      table (if is_cur_mod host then [] else query_of_lid host) (query_of_lid included)
  | NTBinding binding ->
    let lids =
      match binding with
      | Binding_lid (lid, _) -> [lid]
      | Binding_sig (lids, _) -> lids
      | Binding_sig_inst (lids, _, _) -> lids
      | _ -> [] in
    List.fold_left
      (fun tbl lid ->
         let ns_query = if lid.nsstr = cur_mod_str then []
                        else query_of_ids lid.ns in
         CTable.insert
           tbl ns_query (text_of_id lid.ident) lid)
      table lids

let commit_name_tracking' cur_mod names name_events =
  let cur_mod_str = match cur_mod with
                    | None -> "" | Some md -> (SS.mod_name md).str in
  let updater = update_names_from_event cur_mod_str in
  List.fold_left updater names name_events

let commit_name_tracking st name_events =
  let names = commit_name_tracking' st.repl_curmod st.repl_names name_events in
  { st with repl_names = names }

let fresh_name_tracking_hooks () =
  let events = Util.mk_ref [] in
  let push_event evt = events := evt :: !events in
  events,
  { DsEnv.ds_push_module_abbrev_hook =
      (fun dsenv x l -> push_event (NTAlias (DsEnv.current_module dsenv, x, l)));
    DsEnv.ds_push_include_hook =
      (fun dsenv ns -> push_event (NTInclude (DsEnv.current_module dsenv, ns)));
    DsEnv.ds_push_open_hook =
      (fun dsenv op -> push_event (NTOpen (DsEnv.current_module dsenv, op))) },
  { TcEnv.tc_push_in_gamma_hook =
      (fun _ s -> push_event (NTBinding s)) }

let track_name_changes (env: env_t)
    : env_t * (env_t -> env_t * list<name_tracking_event>) =
  let set_hooks dshooks tchooks env =
    let (), tcenv' = with_tcenv env (fun dsenv -> (), DsEnv.set_ds_hooks dsenv dshooks) in
    TcEnv.set_tc_hooks tcenv' tchooks in

  let old_dshooks, old_tchooks = DsEnv.ds_hooks env.dsenv, TcEnv.tc_hooks env in
  let events, new_dshooks, new_tchooks = fresh_name_tracking_hooks () in

  set_hooks new_dshooks new_tchooks env,
  (fun env -> set_hooks old_dshooks old_tchooks env,
           List.rev !events)

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

(** Like ``tc_one_file``, but only return the new environment **)
let tc_one env intf_opt modf =
  let _, env = tc_one_file env intf_opt modf in
  env

(** Load the file or files described by `task`.

``task`` should not be a push fragment. **)
let run_repl_task (curmod: optmod_t) (env: env_t) (task: repl_task) : optmod_t * env_t =
  match task with
  | LDInterleaved (intf, impl) ->
    curmod, tc_one env (Some intf.tf_fname) impl.tf_fname
  | LDSingle intf_or_impl ->
    curmod, tc_one env None intf_or_impl.tf_fname
  | LDInterfaceOfCurrentFile intf ->
    curmod, Universal.load_interface_decls env intf.tf_fname
  | PushFragment frag ->
    tc_one_fragment curmod env (frag, false)

(** Build a list of dependency loading tasks from a list of dependencies **)
let repl_ld_tasks_of_deps (deps: list<string>) (final_tasks: list<repl_task>) =
  let wrap = dummy_tf_of_fname in
  let rec aux deps final_tasks =
    match deps with
    | intf :: impl :: deps' when needs_interleaving intf impl ->
      LDInterleaved (wrap intf, wrap impl) :: aux deps' final_tasks
    | intf_or_impl :: deps' ->
      LDSingle (wrap intf_or_impl) :: aux deps' final_tasks
    | [] -> final_tasks in
  aux deps final_tasks

(** Compute dependencies of `filename` and steps needed to load them.

The dependencies are a list of file name.  The steps are a list of
``repl_task`` elements, to be executed by ``run_repl_task``. **)
let deps_and_repl_ld_tasks_of_our_file filename =
  let get_mod_name fname =
    Parser.Dep.lowercase_module_name fname in
  let our_mod_name =
    get_mod_name filename in
  let has_our_mod_name f =
    (get_mod_name f = our_mod_name) in

  let prims_fname =
    Options.prims () in
  let deps =
    prims_fname ::
    (FStar.Dependencies.find_deps_if_needed
      Parser.Dep.VerifyFigureItOut [filename]) in

  let same_name, real_deps =
    List.partition has_our_mod_name deps in

  let intf_tasks =
    match same_name with
    | [intf; impl] ->
      if not (Parser.Dep.is_interface intf) then
         raise (Err (Util.format1 "Expecting an interface, got %s" intf));
      if not (Parser.Dep.is_implementation impl) then
         raise (Err (Util.format1 "Expecting an implementation, got %s" impl));
      [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)]
    | [impl] ->
      []
    | _ ->
      let mods_str = String.concat " " same_name in
      let message = "Too many or too few files matching %s: %s" in
      raise (Err (Util.format2 message our_mod_name mods_str));
      [] in

  let tasks =
    repl_ld_tasks_of_deps real_deps intf_tasks in
  real_deps, tasks

(** Update timestamps in argument task to last modification times. **)
let update_task_timestamps = function
  | LDInterleaved (intf, impl) ->
    LDInterleaved (tf_of_fname intf.tf_fname, tf_of_fname impl.tf_fname)
  | LDSingle intf_or_impl ->
    LDSingle (tf_of_fname intf_or_impl.tf_fname)
  | LDInterfaceOfCurrentFile intf ->
    LDInterfaceOfCurrentFile (tf_of_fname intf.tf_fname)
  | PushFragment frag -> PushFragment frag

(** Push, run `task`, and pop if it fails.

If `must_rollback` is set, always pop.  Returns a pair: a boolean indicating
success, and a new REPL state. **)
let run_repl_transaction st push_kind must_rollback task =
  let env = push_repl push_kind task st in
  let env, finish_name_tracking = track_name_changes env in // begin name tracking…

  let check_success () =
    get_err_count () = 0 && not must_rollback in

  // Run the task (and capture errors)
  let curmod, env, success =
    match with_captured_errors env
            (fun env -> Some <| run_repl_task st.repl_curmod env task) with
    | Some (curmod, env) when check_success () -> curmod, env, true
    | _ -> st.repl_curmod, env, false in

  let env', name_events = finish_name_tracking env in // …end name tracking
  let st =
    { st with repl_env = env; repl_curmod = curmod } in
  let st =
    if success
    then commit_name_tracking st name_events
    else pop_repl st in

  (success, st)

(** Load dependencies described by `tasks`.

Returns a new REPL state, wrapped in ``Inl`` to indicate complete success or
``Inr`` to indicate a partial failure.  That new state has an updated
``repl_deps_stack``, containing loaded dependencies in reverse order compared to
the original list of tasks: the first dependencies (prims, …) come first; the
current file's interface comes last.

The original value of the ``repl_deps_stack`` field in ``st`` is used to skip
already completed tasks.

This function is stateful: it uses ``push_repl`` and ``pop_repl``. **)
let run_repl_ld_transactions (st: repl_state) (tasks: list<repl_task>) =
  let debug verb task =
    if Options.debug_any () then
      Util.print2 "%s %s" verb (string_of_repl_task task) in

  (* Run as many ``pop_repl`` as there are entries in the input stack.
  Elements of the input stack are expected to match the topmost ones of
  ``!repl_stack`` *)
  let rec revert_many st = function
    | [] -> st
    | (task, _st') :: entries ->
      assert (task = fst (List.hd !repl_stack));
      debug "Reverting" task;
      revert_many (pop_repl st) entries in

  let rec aux (st: repl_state)
              (tasks: list<repl_task>)
              (previous: list<completed_repl_task>) =
    match tasks, previous with
    // All done: return the final state.
    | [], [] ->
      Inl st

    // We have more dependencies to load, and no previously loaded dependencies:
    // run ``task`` and record the updated dependency stack in ``st``.
    | task :: tasks, [] ->
      debug "Loading" task;
      Options.restore_cmd_line_options false |> ignore;
      let timestamped_task = update_task_timestamps task in
      let push_kind = if Options.lax () then LaxCheck else FullCheck in
      let success, st = run_repl_transaction st push_kind false timestamped_task in
      if success then aux ({ st with repl_deps_stack = !repl_stack }) tasks []
      else Inr st

    // We've already run ``task`` previously, and no update is needed: skip.
    | task :: tasks, prev :: previous
        when (fst prev) = (update_task_timestamps task) ->
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

let json_to_str = function
  | JsonNull -> "null"
  | JsonBool b -> Util.format1 "bool (%s)" (if b then "true" else "false")
  | JsonInt i -> Util.format1 "int (%s)" (Util.string_of_int i)
  | JsonStr s -> Util.format1 "string (%s)" s
  | JsonList _ -> "list (...)"
  | JsonAssoc _ -> "dictionary (...)"

exception UnexpectedJsonType of string * json

let js_fail expected got =
  raise (UnexpectedJsonType (expected, got))

let js_int = function
  | JsonInt i -> i
  | other -> js_fail "int" other
let js_str = function
  | JsonStr s -> s
  | other -> js_fail "string" other
let js_list k = function
  | JsonList l -> List.map k l
  | other -> js_fail "list" other
let js_assoc = function
  | JsonAssoc a -> a
  | other -> js_fail "dictionary" other

let js_pushkind s : push_kind = match js_str s with
  | "syntax" -> SyntaxCheck
  | "lax" -> LaxCheck
  | "full" -> FullCheck
  | _ -> js_fail "push_kind" s

let js_reductionrule s = match js_str s with
  | "beta" -> FStar.TypeChecker.Normalize.Beta
  | "delta" -> FStar.TypeChecker.Normalize.UnfoldUntil SS.Delta_constant
  | "iota" -> FStar.TypeChecker.Normalize.Iota
  | "zeta" -> FStar.TypeChecker.Normalize.Zeta
  | "reify" -> FStar.TypeChecker.Normalize.Reify
  | "pure-subterms" -> FStar.TypeChecker.Normalize.PureSubtermsWithinComputations
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
| Pop
| Push of push_query
| VfsAdd of option<string> (* fname *) * string (* contents *)
| AutoComplete of string * completion_context
| Lookup of string * lookup_context * option<position> * list<string>
| Compute of string * option<list<FStar.TypeChecker.Normalize.step>>
| Search of string
| GenericError of string
| ProtocolViolation of string
and query = { qq: query'; qid: string }

let query_needs_current_module = function
  | Exit | DescribeProtocol | DescribeRepl
  | Pop | Push { push_peek_only = false } | VfsAdd _
  | GenericError _ | ProtocolViolation _ -> false
  | Push _ | AutoComplete _ | Lookup _ | Compute _ | Search _ -> true

let interactive_protocol_vernum = 2

let interactive_protocol_features =
  ["autocomplete"; "autocomplete/context";
   "compute"; "compute/reify"; "compute/pure-subterms";
   "describe-protocol"; "describe-repl"; "exit";
   "vfs-add";
   "lookup"; "lookup/context"; "lookup/documentation"; "lookup/definition";
   "peek"; "pop"; "push"; "search"]

exception InvalidQuery of string
type query_status = | QueryOK | QueryNOK | QueryViolatesProtocol

let try_assoc key a =
  Util.map_option snd (Util.try_find (fun (k, _) -> k = key) a)

let wrap_js_failure qid expected got =
  { qid = qid;
    qq = ProtocolViolation (Util.format2 "JSON decoding failed: expected %s, got %s"
                            expected (json_to_str got)) }

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

let read_interactive_query stream : query =
  try
    match Util.read_line stream with
    | None -> raise (ExitREPL 0)
    | Some line ->
      match Util.json_of_string line with
      | None -> { qid = "?"; qq = ProtocolViolation "Json parsing failed." }
      | Some request -> unpack_interactive_query request
  with
  | InvalidQuery msg -> { qid = "?"; qq = ProtocolViolation msg }
  | UnexpectedJsonType (expected, got) -> wrap_js_failure "?" expected got

let json_of_opt json_of_a opt_a =
  Util.dflt JsonNull (Util.map_option json_of_a opt_a)

let json_of_pos pos =
  JsonList [JsonInt (Range.line_of_pos pos); JsonInt (Range.col_of_pos pos)]

let json_of_range_fields file b e =
  JsonAssoc [("fname", JsonStr file);
             ("beg", json_of_pos b);
             ("end", json_of_pos e)]

let json_of_use_range r =
    json_of_range_fields
            (Range.file_of_use_range r)
            (Range.start_of_use_range r)
            (Range.end_of_use_range r)

let json_of_def_range r =
    json_of_range_fields
            (Range.file_of_range r)
            (Range.start_of_range r)
            (Range.end_of_range r)

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

type symbol_lookup_result = { slr_name: string;
                              slr_def_range: option<Range.range>;
                              slr_typ: option<string>;
                              slr_doc: option<string>;
                              slr_def: option<string> }

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

let write_json json =
  Util.print_raw (Util.string_of_json json);
  Util.print_raw "\n"

let write_response qid status response =
  let qid = JsonStr qid in
  let status = match status with
               | QueryOK -> JsonStr "success"
               | QueryNOK -> JsonStr "failure"
               | QueryViolatesProtocol -> JsonStr "protocol-violation" in
  write_json (JsonAssoc [("kind", JsonStr "response");
                         ("query-id", qid);
                         ("status", status);
                         ("response", response)])

let write_message level contents =
  write_json (JsonAssoc [("kind", JsonStr "message");
                         ("level", JsonStr level);
                         ("contents", contents)])

let write_hello () =
  let js_version = JsonInt interactive_protocol_vernum in
  let js_features = JsonList (List.map JsonStr interactive_protocol_features) in
  write_json (JsonAssoc (("kind", JsonStr "protocol-info") :: alist_of_protocol_info))

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
  let filenames (task, _) =
    match task with
    | LDInterleaved (intf, impl) -> [intf.tf_fname; impl.tf_fname]
    | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
    | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
    | PushFragment _ -> [] in

  JsonAssoc
    [("loaded-dependencies",
      JsonList (List.map JsonStr (List.concatMap filenames st.repl_deps_stack)));
     ("options",
      JsonList (List.map json_of_fstar_option (current_fstar_options (fun _ -> true))))]

let with_printed_effect_args k =
  Options.with_saved_options
    (fun () -> Options.set_option "print_effect_args" (Options.Bool true); k ())

let term_to_string tcenv t =
  with_printed_effect_args (fun () -> FStar.TypeChecker.Normalize.term_to_string tcenv t)

let sigelt_to_string se =
  with_printed_effect_args (fun () -> Syntax.Print.sigelt_to_string se)

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

let run_vfs_add st opt_fname contents =
  let fname = Util.dflt st.repl_fname opt_fname in
  Parser.ParseIt.add_vfs_entry fname contents;
  ((QueryOK, JsonNull), Inl st)

let run_pop st =
  if nothing_left_to_pop st then
    ((QueryNOK, JsonStr "Too many pops"), Inl st)
  else
    let st' = pop_repl st in
    ((QueryOK, JsonNull), Inl st')

let collect_errors () =
  let errors = FStar.Errors.report_all() in
  FStar.Errors.clear ();
  errors

(** Compute and load all dependencies of `filename`.

Return an new REPL state wrapped in ``Inr`` in case of failure, and a new REPL
plus with a list of completed tasks wrapped in ``Inl`` in case of success. **)
let load_deps st =
  match with_captured_errors st.repl_env
          (fun _env -> Some <| deps_and_repl_ld_tasks_of_our_file st.repl_fname) with
  | None -> Inr st
  | Some (deps, tasks) ->
    match run_repl_ld_transactions st tasks with
    | Inr st -> Inr st
    | Inl st -> Inl (st, deps)

let rephrase_dependency_error issue =
  { issue with issue_message =
               format1 "Error while computing or loading dependencies:\n%s"
                       issue.issue_message }

let run_push_without_deps st query =
  let { push_code = text; push_line = line; push_column = column;
        push_peek_only = peek_only; push_kind = push_kind } = query in

  TcEnv.toggle_id_info st.repl_env true;
  let frag = { frag_text = text; frag_line = line; frag_col = column } in
  let success, st = run_repl_transaction st push_kind peek_only (PushFragment frag) in

  let status = if success || peek_only then QueryOK else QueryNOK in
  let json_errors = JsonList (collect_errors () |> List.map json_of_issue) in
  let st = if success then { st with repl_line = line; repl_column = column } else st in
  ((status, json_errors), Inl st)

let capitalize str =
  if str = "" then str
  else let first = String.substring str 0 1 in
       String.uppercase first ^ String.substring str 1 (String.length str - 1)

let add_module_completions this_fname deps table =
  let mods =
    FStar.Parser.Dep.build_inclusion_candidates_list () in
  let loaded_mods_set =
    List.fold_left
      (fun acc dep -> psmap_add acc (Parser.Dep.lowercase_module_name dep) true)
      (psmap_empty ()) (Options.prims () :: deps) in // Prims is an implicit dependency
  let loaded modname =
    psmap_find_default loaded_mods_set modname false in
  let this_mod_key =
    Parser.Dep.lowercase_module_name this_fname in
  List.fold_left (fun table (modname, mod_path) ->
      // modname is the filename part of mod_path
      let mod_key = String.lowercase modname in
      if this_mod_key = mod_key then
        table // Exclude current module from completion
      else
        let ns_query = Util.split (capitalize modname) "." in
        CTable.register_module_path table (loaded mod_key) mod_path ns_query)
    table (List.rev mods) // List.rev to process files in order or *increasing* precedence

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
  let tcenv = st.repl_env in

  let info_of_lid_str lid_str =
    let lid = Ident.lid_of_ids (List.map Ident.id_of_text (Util.split lid_str ".")) in
    let lid = Util.dflt lid <| DsEnv.resolve_to_fully_qualified_name tcenv.dsenv lid in
    try_lookup_lid tcenv lid |> Util.map_option (fun ((_, typ), r) -> (Inr lid, typ, r)) in

  let docs_of_lid lid =
    DsEnv.try_lookup_doc tcenv.dsenv lid |> Util.map_option fst in

  let def_of_lid lid =
    Util.bind_opt (TcEnv.lookup_qname tcenv lid) (function
      | (Inr (se, _), _) -> Some (sigelt_to_string se)
      | _ -> None) in

  let info_at_pos_opt =
    Util.bind_opt pos_opt (fun (file, row, col) ->
      TcErr.info_at_pos tcenv file row col) in

  let info_opt =
    match info_at_pos_opt with
    | Some _ -> info_at_pos_opt
    | None -> if symbol = "" then None else info_of_lid_str symbol in

  let response = match info_opt with
    | None -> None
    | Some (name_or_lid, typ, rng) ->
      let name =
        match name_or_lid with
        | Inl name -> name
        | Inr lid -> Ident.string_of_lid lid in
      let typ_str =
        if List.mem "type" requested_info then
          Some (term_to_string tcenv typ)
        else None in
      let doc_str =
        match name_or_lid with
        | Inr lid when List.mem "documentation" requested_info -> docs_of_lid lid
        | _ -> None in
      let def_str =
        match name_or_lid with
        | Inr lid when List.mem "definition" requested_info -> def_of_lid lid
        | _ -> None in
      let def_range =
        if List.mem "defined-at" requested_info then Some rng else None in

      let result = { slr_name = name; slr_def_range = def_range;
                     slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str } in
      Some ("symbol", alist_of_symbol_lookup_result result) in

  match response with
  | None -> Inl "Symbol not found"
  | Some info -> Inr info

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

let code_autocomplete_mod_filter = function
  | _, CTable.Namespace _
  | _, CTable.Module { CTable.mod_loaded = true } -> None
  | pth, CTable.Module md ->
    Some (pth, CTable.Module ({ md with CTable.mod_name = CTable.mod_name md ^ "." }))

let run_code_autocomplete st search_term =
  let needle = Util.split search_term "." in
  let mods_and_nss = CTable.autocomplete_mod_or_ns st.repl_names needle code_autocomplete_mod_filter in
  let lids = CTable.autocomplete_lid st.repl_names needle in
  let json = List.map CTable.json_of_completion_result (lids @ mods_and_nss) in
  ((QueryOK, JsonList json), Inl st)

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

let run_compute st term rules =
  let run_and_rewind st task =
    let env' = push st.repl_env "#compute" in
    let results = task st in
    pop env' "#compute";
    (results, Inl st) in

  let dummy_let_fragment term =
    let dummy_decl = Util.format1 "let __compute_dummy__ = (%s)" term in
    { frag_text = dummy_decl; frag_line = 0; frag_col = 0 } in

  let normalize_term tcenv rules t =
    FStar.TypeChecker.Normalize.normalize rules tcenv t in

  let find_let_body ses =
    match ses with
    | [{ SS.sigel = SS.Sig_let((_, [{ SS.lbunivs = univs; SS.lbdef = def }]), _) }] ->
      Some (univs, def)
    | _ -> None in

  let parse frag =
    match FStar.Parser.ParseIt.parse (Inr frag) with
    | Inl (Inr decls, _) -> Some decls
    | _ -> None in

  let desugar env decls =
    fst (FStar.ToSyntax.ToSyntax.decls_to_sigelts decls env.dsenv) in

  let typecheck tcenv decls =
    let ses, _, _ = FStar.TypeChecker.Tc.tc_decls tcenv decls in
    ses in

  let rules =
    (match rules with
     | Some rules -> rules
     | None -> [FStar.TypeChecker.Normalize.Beta;
               FStar.TypeChecker.Normalize.Iota;
               FStar.TypeChecker.Normalize.Zeta;
               FStar.TypeChecker.Normalize.UnfoldUntil SS.Delta_constant])
    @ [FStar.TypeChecker.Normalize.Inlining;
       FStar.TypeChecker.Normalize.Eager_unfolding;
       FStar.TypeChecker.Normalize.Primops] in

  run_and_rewind st (fun st ->
    let tcenv = st.repl_env in
    let frag = dummy_let_fragment term in
    match st.repl_curmod with
    | None -> (QueryNOK, JsonStr "Current module unset")
    | _ ->
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
            let normalized = normalize_term tcenv rules def in
            (QueryOK, JsonStr (term_to_string tcenv normalized)) in
        if Options.trace_error () then
          aux ()
        else
          try aux ()
          with | e -> (QueryNOK, (match FStar.Errors.issue_of_exn e with
                                  | Some issue -> JsonStr (FStar.Errors.format_issue issue)
                                  | None -> raise e)))

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
  match q with // First handle queries that support both partial and full states…
  | Exit -> run_exit st
  | DescribeProtocol -> run_describe_protocol st
  | DescribeRepl -> run_describe_repl st
  | GenericError message -> run_generic_error st message
  | ProtocolViolation query -> run_protocol_violation st query
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

let rec go st : int =
  let rec loop st : int =
    let query = validate_query st (read_interactive_query st.repl_stdin) in
    let (status, response), state_opt = run_query st query.qq in
    write_response query.qid status response;
    match state_opt with
    | Inl st' -> loop st'
    | Inr exitcode -> raise (ExitREPL exitcode) in

  if Options.trace_error () then
    loop st
  else
    try loop st with ExitREPL n -> n

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

let interactive_printer =
  { printer_prinfo = (fun s -> write_message "info" (JsonStr s));
    printer_prwarning = (fun s -> write_message "warning" (JsonStr s));
    printer_prerror = (fun s -> write_message "error" (JsonStr s));
    printer_prgeneric = (fun label get_string get_json -> write_message label (get_json ()) )}

let initial_range =
  Range.mk_range "<input>" (Range.mk_pos 1 0) (Range.mk_pos 1 0)

let interactive_mode' (filename: string): unit =
  write_hello ();

  let env = init_env () in
  let env = FStar.TypeChecker.Env.set_range env initial_range in

  let init_st =
    { repl_line = 1; repl_column = 0; repl_fname = filename;
      repl_curmod = None; repl_env = env; repl_deps_stack = [];
      repl_stdin = open_stdin ();
      repl_names = CompletionTable.empty } in

  let exit_code =
    if FStar.Options.record_hints() || FStar.Options.use_hints() then
      FStar.SMTEncoding.Solver.with_hints_db (List.hd (Options.file_list ())) (fun () -> go init_st)
    else
      go init_st in
  exit exit_code

let interactive_mode (filename:string): unit =
  FStar.Util.set_printer interactive_printer;

  if Options.verify_module () <> [] then
     Util.print_warning "--ide: ignoring --verify_module";

  if Option.isSome (Options.codegen ()) then
    Util.print_warning "--ide: ignoring --codegen";

  if Options.trace_error () then
    // This prevents the error catcher below from swallowing backtraces
    interactive_mode' filename
  else
    try
      FStar.Errors.set_handler interactive_error_handler;
      interactive_mode' filename
    with
    | e -> (// Revert to default handler since we won't have an opportunity to
           // print errors ourselves.
           FStar.Errors.set_handler FStar.Errors.default_handler;
           raise e)
