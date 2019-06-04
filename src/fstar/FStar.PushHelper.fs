(* FStar.Interactive.Lsp and FStar.Interactive.Ide need to push various *
 * text fragments and update state; this file collects helpers for them *)
#light "off"

module FStar.PushHelper
open FStar.ST
open FStar.All
open FStar.Util
open FStar.Ident
open FStar.Errors
open FStar.Universal
open FStar.JsonHelper
open FStar.Parser.ParseIt
open FStar.TypeChecker.Env

module U = FStar.Util
module SS = FStar.Syntax.Syntax
module DsEnv = FStar.Syntax.DsEnv
module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable

type push_kind = | SyntaxCheck | LaxCheck | FullCheck
type ctx_depth_t = int * int * solver_depth_t * int
type deps_t = FStar.Parser.Dep.deps
type either_replst = either<repl_state, repl_state>

let repl_stack: ref<repl_stack_t> = U.mk_ref []

let set_check_kind env check_kind =
  { env with lax = (check_kind = LaxCheck);
             dsenv = DsEnv.set_syntax_only env.dsenv (check_kind = SyntaxCheck)}

(** Build a list of dependency loading tasks from a list of dependencies **)
let repl_ld_tasks_of_deps (deps: list<string>) (final_tasks: list<repl_task>) =
  let wrap fname = { tf_fname = fname; tf_modtime = U.now () } in
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
let deps_and_repl_ld_tasks_of_our_file filename
    : list<string>
    * list<repl_task>
    * FStar.Parser.Dep.deps =
  let get_mod_name fname =
    Parser.Dep.lowercase_module_name fname in
  let our_mod_name =
    get_mod_name filename in
  let has_our_mod_name f =
    (get_mod_name f = our_mod_name) in

  let parse_data_cache = FStar.CheckedFiles.load_parsing_data_from_cache in
  let deps, dep_graph = FStar.Dependencies.find_deps_if_needed [filename] parse_data_cache in
  let same_name, real_deps =
    List.partition has_our_mod_name deps in

  let intf_tasks =
    match same_name with
    | [intf; impl] ->
      if not (Parser.Dep.is_interface intf) then
         raise_err (Errors.Fatal_MissingInterface, U.format1 "Expecting an interface, got %s" intf);
      if not (Parser.Dep.is_implementation impl) then
         raise_err (Errors.Fatal_MissingImplementation,
                    U.format1 "Expecting an implementation, got %s" impl);
      [LDInterfaceOfCurrentFile ({ tf_fname = intf; tf_modtime = U.now () }) ]
    | [impl] ->
      []
    | _ ->
      let mods_str = String.concat " " same_name in
      let message = "Too many or too few files matching %s: %s" in
      raise_err (Errors.Fatal_TooManyOrTooFewFileMatch,
                 (U.format message [our_mod_name; mods_str]));
      [] in

  let tasks =
    repl_ld_tasks_of_deps real_deps intf_tasks in
  real_deps, tasks, dep_graph

(** Checkpoint the current (typechecking and desugaring) environment **)
let snapshot_env env msg : repl_depth_t * env_t =
  let ctx_depth, env = TypeChecker.Tc.snapshot_context env msg in
  let opt_depth, () = Options.snapshot () in
  (ctx_depth, opt_depth), env

let push_repl msg push_kind task st =
  let depth, env = snapshot_env st.repl_env msg in
  repl_stack := (depth, (task, st)) :: !repl_stack;
  { st with repl_env = set_check_kind env push_kind } // repl_env is the only mutable part of st

(** Revert to a previous checkpoint.

Usage note: A proper push/pop pair looks like this:

  let noop =
    let env', depth = snapshot_env env in
    // [Do stuff with env']
    let env'' = rollback_env env'.solver depth in
    env''

In most cases, the invariant should hold that ``env'' === env`` (look for
assertions of the form ``physical_equality _ _`` in the sources).

You may be wondering why we need ``snapshot`` and ``rollback``.  Aren't ``push``
and ``pop`` sufficient?  They are not.  The issue is that the typechecker's code
can encounter (fatal) errors at essentially any point, and was not written to
clean up after itself in these cases.  Fatal errors are handled by raising an
exception, skipping all code that would ``pop`` previously pushed state.

That's why we need ``rollback``: all that rollback does is call ``pop``
sufficiently many times to get back into the state we were before the
corresponding ``pop``. **)
let rollback_env solver msg (ctx_depth, opt_depth) =
  let env = TypeChecker.Tc.rollback_context solver msg (Some ctx_depth) in
  Options.rollback (Some opt_depth);
  env

let pop_repl msg st =
  match !repl_stack with
  | [] -> failwith "Too many pops"
  | (depth, (_, st')) :: stack_tl ->
    let env = rollback_env st.repl_env.solver msg depth in
    repl_stack := stack_tl;
    // Because of the way ``snapshot`` is implemented, the `st'` and `env`
    // that we rollback to should be consistent:
    FStar.Common.runtime_assert
      (U.physical_equality env st'.repl_env)
      "Inconsistent stack state";
    st'

(** Like ``tc_one_file``, but only return the new environment **)
let tc_one (env:env_t) intf_opt modf =
  let parse_data = modf |> FStar.Parser.Dep.parsing_data_of (TcEnv.dep_graph env) in
  let _, env = tc_one_file_for_ide env intf_opt modf parse_data in
  env

(** Load the file or files described by `task` **)
let run_repl_task (curmod: optmod_t) (env: env_t) (task: repl_task) : optmod_t * env_t =
  match task with
  | LDInterleaved (intf, impl) ->
    curmod, tc_one env (Some intf.tf_fname) impl.tf_fname
  | LDSingle intf_or_impl ->
    curmod, tc_one env None intf_or_impl.tf_fname
  | LDInterfaceOfCurrentFile intf ->
    curmod, Universal.load_interface_decls env intf.tf_fname
  | PushFragment frag ->
    tc_one_fragment curmod env frag
  | Noop ->
    curmod, env

(*******************************************)
(* Name tracking: required for completions *)
(*******************************************)

type name_tracking_event =
| NTAlias of lid (* host *) * ident (* alias *) * lid (* aliased *)
| NTOpen of lid (* host *) * DsEnv.open_module_or_namespace (* opened *)
| NTInclude of lid (* host *) * lid (* included *)
| NTBinding of either<FStar.Syntax.Syntax.binding, TcEnv.sig_binding>

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
      | Inl (SS.Binding_lid (lid, _)) -> [lid]
      | Inr (lids, _) -> lids
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
    let (), tcenv' = with_dsenv_of_tcenv env (fun dsenv -> (), DsEnv.set_ds_hooks dsenv dshooks) in
    TcEnv.set_tc_hooks tcenv' tchooks in

  let old_dshooks, old_tchooks = DsEnv.ds_hooks env.dsenv, TcEnv.tc_hooks env in
  let events, new_dshooks, new_tchooks = fresh_name_tracking_hooks () in

  set_hooks new_dshooks new_tchooks env,
  (fun env -> set_hooks old_dshooks old_tchooks env,
           List.rev !events)

// A REPL transaction with different error handling; used exclusively by LSP;
// variant of run_repl_transaction in IDE
let repl_tx st push_kind task =
  try
    let st = push_repl "repl_tx" push_kind task st in
    let env, finish_name_tracking = track_name_changes st.repl_env in // begin name tracking
    let curmod, env = run_repl_task st.repl_curmod env task in
    let st = { st with repl_curmod = curmod; repl_env = env } in
    let env, name_events = finish_name_tracking env in // end name tracking
    None, commit_name_tracking st name_events
  with
  | Failure (msg) ->
    Some (js_diag st.repl_fname msg None), st
  | U.SigInt ->
    U.print_error "[E] Interrupt"; None, st
  | Error (e, msg, r) ->
    Some (js_diag st.repl_fname msg (Some r)), st
  | Err (e, msg) ->
    Some (js_diag st.repl_fname msg None), st
  | Stop ->
    U.print_error "[E] Stop"; None, st

// Little helper
let tf_of_fname fname =
  { tf_fname = fname;
    tf_modtime = Parser.ParseIt.get_file_last_modification_time fname }

// Little helper: update timestamps in argument task to last modification times.
let update_task_timestamps = function
  | LDInterleaved (intf, impl) ->
    LDInterleaved (tf_of_fname intf.tf_fname, tf_of_fname impl.tf_fname)
  | LDSingle intf_or_impl ->
    LDSingle (tf_of_fname intf_or_impl.tf_fname)
  | LDInterfaceOfCurrentFile intf ->
    LDInterfaceOfCurrentFile (tf_of_fname intf.tf_fname)
  | other -> other

// Variant of run_repl_ld_transactions in IDE; used exclusively by LSP.
// The first dependencies (prims, ...) come first; the current file's
// interface comes last. The original value of the `repl_deps_stack` field
// in ``st`` is used to skip already completed tasks.
let repl_ldtx (st: repl_state) (tasks: list<repl_task>) : either_replst =

  (* Run as many ``pop_repl`` as there are entries in the input stack.
  Elements of the input stack are expected to match the topmost ones of
  ``!repl_stack`` *)
  let rec revert_many st = function
    | [] -> st
    | (_id, (task, _st')) :: entries ->
      let st' = pop_repl "repl_ldtx" st in
      let dep_graph = TcEnv.dep_graph st.repl_env in
      let st' = { st' with repl_env = TcEnv.set_dep_graph st'.repl_env dep_graph } in
      revert_many st' entries in

  let rec aux (st: repl_state)
              (tasks: list<repl_task>)
              (previous: list<repl_stack_entry_t>) =
    match tasks, previous with
    // All done: return the final state.
    | [], [] -> Inl st

    // We have more dependencies to load, and no previously loaded dependencies:
    // run ``task`` and record the updated dependency stack in ``st``.
    | task :: tasks, [] ->
      let timestamped_task = update_task_timestamps task in
      let diag, st = repl_tx st LaxCheck timestamped_task in
      if not (U.is_some diag) then aux ({ st with repl_deps_stack = !repl_stack }) tasks []
      else Inr st

    // We've already run ``task`` previously, and no update is needed: skip.
    | task :: tasks, prev :: previous
        when fst (snd prev) = update_task_timestamps task ->
      aux st tasks previous

    // We have a timestamp mismatch or a new dependency:
    // revert now-obsolete dependencies and resume loading.
    | tasks, previous ->
      aux (revert_many st previous) tasks [] in

  aux st tasks (List.rev st.repl_deps_stack)

// Variant of load_deps in IDE; used exclusively by LSP
let ld_deps st =
  try
    let (deps, tasks, dep_graph) = deps_and_repl_ld_tasks_of_our_file st.repl_fname in
    let st = { st with repl_env = TcEnv.set_dep_graph st.repl_env dep_graph } in
    match repl_ldtx st tasks with
    | Inr st -> Inr st
    | Inl st -> Inl (st, deps)
  with
  | _ -> U.print_error "[E] Failed to load deps"; Inr st

let add_module_completions this_fname deps table =
  let capitalize str = if str = "" then str
                       else let first = String.substring str 0 1 in
                       String.uppercase first ^ String.substring str 1 (String.length str - 1) in
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

// Variant of run_push_with_deps in IDE; used exclusively by LSP
let full_lax text st =
  TcEnv.toggle_id_info st.repl_env true;
  let frag = { frag_fname = st.repl_fname; frag_text = text; frag_line = 1; frag_col = 0 } in
  match ld_deps st with
  | Inl (st, deps) ->
      let names = add_module_completions st.repl_fname deps st.repl_names in
      repl_tx ({ st with repl_names = names }) LaxCheck (PushFragment frag)
  | Inr st -> None, st
