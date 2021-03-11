#light "off"
module FStar.Tactics.Types

open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common

module Env     = FStar.TypeChecker.Env
module O       = FStar.Options
module SS      = FStar.Syntax.Subst
module Cfg     = FStar.TypeChecker.Cfg
module N       = FStar.TypeChecker.Normalize
module Range   = FStar.Range
module BU      = FStar.Util
module S       = FStar.Syntax.Syntax
module U       = FStar.Syntax.Util

(*
   f: x:int -> P
   ==================
      P
 *)
//A goal is typically of the form
//    G |- ?u : t
// where context = G
//       witness = ?u, although, more generally, witness is a partial solution and can be any term
//       goal_ty = t
//
// INVARIANT: goal_main_env.gamma is EQUAL to goal_ctx_uvar.ctx_uvar_gamma
type goal = {
    goal_main_env : env;
    goal_ctx_uvar : ctx_uvar;
    opts    : O.optionstate; // option state for this particular goal
    is_guard : bool; // Marks whether this goal arised from a guard during tactic runtime
                     // We make the distinction to be more user-friendly at times
    label : string; // A user-defined description
}
let goal_env g = g.goal_main_env
let goal_witness g =
    FStar.Syntax.Syntax.mk (Tm_uvar (g.goal_ctx_uvar, ([], NoUseRange))) Range.dummyRange
let goal_type g = g.goal_ctx_uvar.ctx_uvar_typ

let goal_with_type g t : goal =
    let c = g.goal_ctx_uvar in
    let c' = {c with ctx_uvar_typ = t} in
    { g with goal_ctx_uvar = c' }

let goal_with_env g env : goal =
    let c = g.goal_ctx_uvar in
    let c' = {c with ctx_uvar_gamma = env.gamma ; ctx_uvar_binders = Env.all_binders env } in
    { g with goal_main_env=env; goal_ctx_uvar = c' }

(* Unsafe? *)
let goal_of_ctx_uvar (g:goal) (ctx_u : ctx_uvar) : goal =
    { g with goal_ctx_uvar = ctx_u }

let mk_goal env u o b l = {
    goal_main_env=env;
    goal_ctx_uvar=u;
    opts=o;
    is_guard=b;
    label=l;
}

let goal_of_goal_ty env typ : goal * guard_t =
    let u, ctx_uvars, g_u =
        Env.new_implicit_var_aux "proofstate_of_goal_ty" typ.pos env typ Allow_untyped None
    in
    let ctx_uvar, _ = List.hd ctx_uvars in
    let g = mk_goal env ctx_uvar (FStar.Options.peek()) false "" in
    g, g_u

let goal_of_implicit env (i:Env.implicit) : goal =
  mk_goal ({env with gamma=i.imp_uvar.ctx_uvar_gamma}) i.imp_uvar (FStar.Options.peek()) false i.imp_reason

let rename_binders subst bs =
    bs |> List.map (function b ->
        let x = b.binder_bv in
        let y = SS.subst subst (S.bv_to_name x) in
        match (SS.compress y).n with
        | Tm_name y ->
            // We don't want to change the type
            { b with binder_bv = { b.binder_bv with sort = SS.subst subst x.sort } }
        | _ -> failwith "Not a renaming")

(* This is only for show: this goal becomes ill-formed since it does
 * not satisfy the invariant on gamma *)
let subst_goal subst goal =
    let g = goal.goal_ctx_uvar in
    let ctx_uvar = {
        g with ctx_uvar_gamma=Env.rename_gamma subst g.ctx_uvar_gamma;
               ctx_uvar_binders=rename_binders subst g.ctx_uvar_binders;
               ctx_uvar_typ=SS.subst subst g.ctx_uvar_typ;
    } in
    { goal with goal_ctx_uvar = ctx_uvar }

type guard_policy =
    | Goal
    | SMT
    | Force
    | Drop // unsound

type proofstate = {
    main_context : env;          //the shared top-level context for all goals
    all_implicits: implicits ;   //all the implicits currently open, partially resolved

    // NOTE: Goals are user-settable, the "goals" we mean in
    // the paper are the implicits above, these are simply a
    // way for primitives to take/give goals, and a way
    // to have the SMT goal set. What we should really do
    // is go full-LCF and take them as arguments, returning them
    // as values. This option stack should be user-level.
    goals        : list<goal>;   //all the goals remaining to be solved
    smt_goals    : list<goal>;   //goals that have been deferred to SMT

    depth        : int;          //depth for tracing and debugging
    __dump       : proofstate -> string -> unit; // callback to dump_proofstate, to avoid an annoying circularity

    psc          : Cfg.psc;        //primitive step context where we started execution
    entry_range  : Range.range;  //position of entry, set by the use
    guard_policy : guard_policy; //guard policy: what to do with guards arising during tactic exec
    freshness    : int;          //a simple freshness counter for the fresh tactic
    tac_verb_dbg : bool;         //whether to print verbose debugging messages

    local_state  : BU.psmap<term>; // local metaprogram state
    urgency      : int;          // When printing a proofstate due to an error, this
                                 // is used by emacs to decide whether it should pop
                                 // open a buffer or not (default: 1).
}

let subst_proof_state subst ps =
    if O.tactic_raw_binders ()
    then ps
    else { ps with goals = List.map (subst_goal subst) ps.goals
    }

let decr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth - 1 }

let incr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth + 1 }

let set_ps_psc psc ps = { ps with psc = psc }

let tracepoint_with_psc psc ps : bool =
    if O.tactic_trace () || (ps.depth <= O.tactic_trace_d ()) then begin
        let ps = set_ps_psc psc ps in
        let subst = Cfg.psc_subst ps.psc in
        ps.__dump (subst_proof_state subst ps) "TRACE"
    end;
    true

let tracepoint ps : bool =
    if O.tactic_trace () || (ps.depth <= O.tactic_trace_d ()) then begin
        let subst = Cfg.psc_subst ps.psc in
        ps.__dump (subst_proof_state subst ps) "TRACE"
    end;
    true

let set_proofstate_range ps r =
    { ps with entry_range = Range.set_def_range ps.entry_range (Range.def_range r) }

let goals_of     ps : list<goal> = ps.goals
let smt_goals_of ps : list<goal> = ps.smt_goals

let is_guard g = g.is_guard

let get_label g = g.label
let set_label l g = { g with label = l }

type direction =
    | TopDown
    | BottomUp

type ctrl_flag =
    | Continue
    | Skip
    | Abort

let check_goal_solved' goal =
  match FStar.Syntax.Unionfind.find goal.goal_ctx_uvar.ctx_uvar_head with
  | Some t -> Some t
  | None   -> None

let check_goal_solved goal =
  Option.isSome (check_goal_solved' goal)

let get_phi (g:goal) : option<term> =
    U.un_squash (N.unfold_whnf (goal_env g) (goal_type g))

let is_irrelevant (g:goal) : bool =
    Option.isSome (get_phi g)
