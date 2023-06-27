(*
   Copyright 2008-2016 Microsoft Research

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
module FStar.Tactics.Types

open FStar.Compiler.Effect
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.Tactics.Common
module Cfg = FStar.TypeChecker.Cfg
module N = FStar.TypeChecker.Normalize
module Range = FStar.Compiler.Range
module BU = FStar.Compiler.Util
module O = FStar.Options

module Core = FStar.TypeChecker.Core

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
    goal_main_env: env;
    goal_ctx_uvar : ctx_uvar;
    opts    : FStar.Options.optionstate; // option state for this particular goal
    is_guard : bool; // Marks whether this goal arose from a guard during tactic runtime
                     // We make the distinction to be more user-friendly at times
    label : string; // A user-defined description
}
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
    // as values. This goal stack should be user-level.
    goals        : list goal;   //all the goals remaining to be solved
    smt_goals    : list goal;   //goals that have been deferred to SMT

    depth        : int;          //depth for tracing and debugging
    __dump       : proofstate -> string -> unit; // callback to dump_proofstate, to avoid an annoying circularity
    psc          : Cfg.psc;        //primitive step context where we started execution
    entry_range  : Range.range;  //position of entry, set by the use
    guard_policy : guard_policy; //guard policy: what to do with guards arising during tactic exec
    freshness    : int;          //a simple freshness counter for the fresh tactic
    tac_verb_dbg : bool;         //whether to print verbose debugging messages

    local_state  : BU.psmap term; // local metaprogram state

    urgency      : int;          // When printing a proofstate due to an error, this
                                 // is used by emacs to decide whether it should pop
                                 // open a buffer or not (default: 1).
}

val decr_depth : proofstate -> proofstate
val incr_depth : proofstate -> proofstate
val tracepoint_with_psc : Cfg.psc -> proofstate -> bool
val tracepoint : proofstate -> bool
val set_proofstate_range : proofstate -> Range.range -> proofstate

val set_ps_psc : Cfg.psc -> proofstate -> proofstate
val goal_env: goal -> env
val goal_witness: goal -> term
val goal_type: goal -> term
val goal_with_env: goal -> env -> goal
val is_guard : goal -> bool

val get_label : goal -> string
val set_label : string -> goal -> goal

val goals_of     : proofstate -> list goal
val smt_goals_of : proofstate -> list goal

val mk_goal: env -> ctx_uvar -> FStar.Options.optionstate -> bool -> string -> goal

val goal_of_goal_ty : env -> typ -> goal * guard_t
val goal_of_implicit : env -> implicit -> goal
val goal_of_ctx_uvar: goal -> ctx_uvar -> goal

type ctrl_flag =
    | Continue
    | Skip
    | Abort

type direction =
    | TopDown
    | BottomUp

val check_goal_solved' : goal -> option term
val check_goal_solved  : goal -> bool
val get_phi            : goal -> option term
val is_irrelevant      : goal -> bool

type unfold_side =
  | Left
  | Right
  | Both
  | Neither

type tot_or_ghost =
  | E_Total
  | E_Ghost


(*** These are here for userspace, the library has an interface into this module. *)
(* Typing reflection *)
val subtyping_token (g:env) (t0 t1:typ) : Type0
val equiv_token (g:env) (t0 t1:typ) : Type0
val typing_token (g:env) (e:term) (c:tot_or_ghost & typ) : Type0
val match_complete_token (g:env) (sc:term) (t:typ) (pats:list pattern) : Type0
let issues = list FStar.Issue.issue
