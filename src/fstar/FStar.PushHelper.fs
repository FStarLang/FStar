(* FStar.Interactive.Lsp and FStar.Interactive.Ide need to push various *
 * text fragments and update state; this file collects helpers for them *)
#light "off"

module FStar.PushHelper
open FStar.ST
open FStar.All
open FStar.Universal
open FStar.Errors
open FStar.JsonHelper
open FStar.TypeChecker.Env
open FStar.Parser.ParseIt

module U = FStar.Util
module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
module DsEnv = FStar.Syntax.DsEnv

type push_kind = | SyntaxCheck | LaxCheck | FullCheck
type ctx_depth_t = int * int * solver_depth_t * int
type deps_t = FStar.Parser.Dep.deps

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

// Variant of load_deps in IDE; used exclusively by LSP
let ld_deps st =
  try
    let (deps, _, _) = deps_and_repl_ld_tasks_of_our_file st.repl_fname in
    deps
  with
  | _ -> U.print_error "[E] Failed to load deps"; []

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

// A REPL transaction without name-tracking; used exclusively by LSP;
// variant of run_repl_transaction in IDE
let repl_tx st push_kind task =
  let st = push_repl "repl_tx" push_kind task st in

  try
    let curmod, env = run_repl_task st.repl_curmod st.repl_env task in
    let st = { st with repl_curmod = curmod; repl_env = env } in
    true, st
  with
  | Failure (msg) ->
    U.print1_error "[F] %s" msg; false, pop_repl "run_tx" st
  | U.SigInt ->
    U.print_error "[E] Interrupt"; false, pop_repl "run_tx" st
  | Error (e, msg, r) ->
    U.print1_error "[E] %s" msg; false, pop_repl "run_tx" st
  | Err (e, msg) ->
    U.print1_error "[E] %s" msg; false, pop_repl "run_tx" st
  | Stop ->
    U.print_error "[E] Stop"; false, pop_repl "run_tx" st

let full_lax text st =
  let frag = { frag_text = text; frag_line = 1; frag_col = 0 } in
  let _, st = repl_tx st LaxCheck (PushFragment frag) in
  st