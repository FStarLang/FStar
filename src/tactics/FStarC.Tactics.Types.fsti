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
module FStarC.Tactics.Types

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.Tactics.Common
open FStarC.Class.Show
open FStarC.Class.PP

module PO      = FStarC.TypeChecker.Primops
module Range   = FStarC.Range

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
    opts    : FStarC.Options.optionstate; // option state for this particular goal
    is_guard : bool; // Marks whether this goal arose from a guard during tactic runtime
                     // We make the distinction to be more user-friendly at times
    label : string; // A user-defined description
}
type guard_policy =
    | Goal
    | SMT
    | SMTSync
    | Force
    | ForceSMT
    | Drop // unsound

instance val showable_guard_policy : showable guard_policy
instance val pretty_guard_policy   : pretty guard_policy

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

    // These are read-only, for splice tactics to read.
    // They are just empty in other invocations.
    splice_quals : list qualifier;
    splice_attrs : list attribute;

    depth        : int;          //depth for tracing and debugging
    __dump       : proofstate -> string -> unit; // callback to dump_proofstate, to avoid an annoying circularity
    psc          : PO.psc;       //primitive step context where we started execution
    entry_range  : Range.t;  //position of entry, set by the use
    guard_policy : guard_policy; //guard policy: what to do with guards arising during tactic exec
    freshness    : int;          //a simple freshness counter for the fresh tactic
    tac_verb_dbg : bool;         //whether to print verbose debugging messages

    local_state  : PSMap.t term; // local metaprogram state

    urgency      : int;          // When printing a proofstate due to an error, this
                                 // is used by emacs to decide whether it should pop
                                 // open a buffer or not (default: 1).

    dump_on_failure : bool;      // Whether to dump the proofstate to the user when a failure occurs.
}

type ref_proofstate = ref proofstate

val decr_depth : proofstate -> proofstate
val incr_depth : proofstate -> proofstate
val tracepoint_with_psc : PO.psc -> proofstate -> bool
val tracepoint : proofstate -> bool
val set_proofstate_range : proofstate -> Range.t -> proofstate

val set_ps_psc : PO.psc -> proofstate -> proofstate
val goal_env: goal -> env
val goal_range: goal -> Range.t
val goal_witness: goal -> term
val goal_type: goal -> term
val goal_opts: goal -> Options.optionstate
val goal_with_env: goal -> env -> goal
val is_guard : goal -> bool

val get_label : goal -> string
val set_label : string -> goal -> goal

val goals_of     : proofstate -> list goal
val smt_goals_of : proofstate -> list goal

val mk_goal: env -> ctx_uvar -> FStarC.Options.optionstate -> bool -> string -> goal

val goal_of_goal_ty : env -> typ -> goal & guard_t
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

type tref (a:Type) = ref a
