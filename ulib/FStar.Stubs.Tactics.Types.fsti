(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Stubs.Tactics.Types

open FStar.Stubs.Reflection.Types
include FStar.Stubs.Tactics.Common
include FStar.Stubs.TypeChecker.Core

assume new type goal
assume new type proofstate

(* Returns the active goals *)
val goals_of     : proofstate -> list goal
(* Returns the goals marked for SMT *)
val smt_goals_of : proofstate -> list goal

(* Inspecting a goal *)
val goal_env     : goal -> env
val goal_type    : goal -> typ
val goal_witness : goal -> term
val is_guard     : goal -> bool (* A bit of helper info: did this goal come from a VC guard? *)

val get_label    : goal -> string
val set_label    : string -> goal -> goal

(* Tracing *)
val incr_depth : proofstate -> proofstate
val decr_depth : proofstate -> proofstate
(* [tracepoint] always returns true. We do not use unit to prevent
erasure. *)
val tracepoint : proofstate -> b:bool{b == true}
val set_proofstate_range : proofstate -> FStar.Range.range -> proofstate

type direction =
    | TopDown
    | BottomUp

type ctrl_flag =
    | Continue
    | Skip
    | Abort

type guard_policy =
    | Goal      // Add guards as (normal) goals
    | SMT       // Add guards as SMT goals
    | SMTSync   // Send guards to SMT immediately, will *log* errors (not raise) if anything fails
    | Force     // Force guards without SMT, immediately. Raises an exception on failure.
    | ForceSMT  // Force guards with SMT, immediately. Raises an exception on failure.
    | Drop      // Drop guards, clearly unsound! careful!

(* Typing reflection *)
val non_informative_token (g:env) (t:typ) : Type0
val subtyping_token (g:env) (t0 t1:typ) : Type0
val equiv_token (g:env) (t0 t1:typ) : Type0
val typing_token (g:env) (e:term) (c:tot_or_ghost & typ) : Type0

(* Must be inline, this definition is not there in src/FStar.Tactics.Types *)
inline_for_extraction
let issues = list FStar.Issue.issue

val tref (a:Type) : Type0
