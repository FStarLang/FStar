#light "off"
module FStar.Tactics.Types

open FStar.All
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
module Env = FStar.TypeChecker.Env
module Options = FStar.Options
module SS = FStar.Syntax.Subst
module Cfg = FStar.TypeChecker.Cfg
module N = FStar.TypeChecker.Normalize
module Range = FStar.Range
module BU = FStar.Util

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
type goal = {
    goal_main_env : env;
    goal_ctx_uvar : ctx_uvar;
    opts    : FStar.Options.optionstate; // option state for this particular goal
    is_guard : bool; // Marks whether this goal arised from a guard during tactic runtime
                     // We make the distinction to be more user-friendly at times
    label : string; // A user-defined description
}
let goal_env g = { g.goal_main_env with gamma = g.goal_ctx_uvar.ctx_uvar_gamma }
let goal_witness g =
    FStar.Syntax.Syntax.mk (Tm_uvar (g.goal_ctx_uvar, ([], NoUseRange))) None Range.dummyRange
let goal_type g = g.goal_ctx_uvar.ctx_uvar_typ
let goal_with_type g t =
    let c = g.goal_ctx_uvar in
    let c' = {c with ctx_uvar_typ = t} in
    { g with goal_ctx_uvar = c' }
let goal_with_env g env =
    let c = g.goal_ctx_uvar in
    let c' = {c with ctx_uvar_gamma = env.gamma ; ctx_uvar_binders = Env.all_binders env } in
    { g with goal_main_env=env; goal_ctx_uvar = c' }

let mk_goal env u o b l = {
    goal_main_env=env;
    goal_ctx_uvar=u;
    opts=o;
    is_guard=b;
    label=l;
}

let subst_goal subst goal =
    let g = goal.goal_ctx_uvar in
    let ctx_uvar = {
        g with ctx_uvar_gamma=Env.rename_gamma subst g.ctx_uvar_gamma;
               ctx_uvar_typ=SS.subst subst g.ctx_uvar_typ
    } in
    { goal with goal_ctx_uvar = ctx_uvar }

type guard_policy =
    | Goal
    | SMT
    | Force
    | Drop // unsound

type proofstate = {
    main_context : env;          //the shared top-level context for all goals
    main_goal    : goal;         //this is read only; it helps keep track of the goal we started working on initially
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
}

let subst_proof_state subst ps =
    if Options.tactic_raw_binders ()
    then ps
    else { ps with main_goal = subst_goal subst ps.main_goal;
                   goals = List.map (subst_goal subst) ps.goals
    }

let decr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth - 1 }

let incr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth + 1 }

let tracepoint ps : unit =
    if Options.tactic_trace () || (ps.depth <= Options.tactic_trace_d ())
    then ps.__dump (subst_proof_state (Cfg.psc_subst ps.psc) ps) "TRACE"
    else ()

let set_ps_psc psc ps = { ps with psc = psc }

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

exception TacticFailure of string
exception EExn of term
