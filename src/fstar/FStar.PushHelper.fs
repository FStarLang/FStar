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

module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
module DsEnv = FStar.Syntax.DsEnv

type push_kind = | SyntaxCheck | LaxCheck | FullCheck
type ctx_depth_t = int * int * solver_depth_t * int

let repl_stack: ref<repl_stack_t> = Util.mk_ref []

let set_check_kind env check_kind =
  { env with lax = (check_kind = LaxCheck);
             dsenv = DsEnv.set_syntax_only env.dsenv (check_kind = SyntaxCheck)}

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
      (Util.physical_equality env st'.repl_env)
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

let repl_tx st push_kind task =
  let st = push_repl "repl_tx" push_kind task st in
  let check_success () = get_err_count () = 0 in

  // Run the task (and capture errors)
  try
    let curmod, env = run_repl_task st.repl_curmod st.repl_env task in
    let st = { st with repl_curmod = curmod; repl_env = env } in
    (true, st)
  with
    | _ -> (false, pop_repl "run_tx" st)