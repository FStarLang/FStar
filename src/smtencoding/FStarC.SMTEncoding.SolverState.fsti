(*
   Copyright 2024 Microsoft Research

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
module FStarC.SMTEncoding.SolverState
(**
  This module is an abstraction of state of the SMT solver, expressed in terms of the facts
  that are visible to it currently.

  As such, it also encapsulates the various notions of filtering the facts that
  are sent to the solver, including:

    - Filtering with unsat cores
    - Context pruning
    - Filtering using the using_facts_from setting

  This interface is purely functional: every operation takes the current state and 
  optionally returns a new one, in case the state changes.

  Note, this module does not directly call the SMT solver itself: That is
  handled in FStarC.SMTEncoding.Z3.fst. Instead, it buffers all Term.decls to be
  sent to the solver and a call to flush returns all the decls to be sent.
*)
open FStarC.Effect
open FStar open FStarC
open FStarC
open FStarC.SMTEncoding.Term
open FStarC.BaseTypes
open FStarC.Util
module BU = FStarC.Util
module U = FStarC.SMTEncoding.UnsatCore
type using_facts_from_setting = list (list string & bool)

// Abstract state of the solver
val solver_state : Type0

// Initialize the solver state
val init (_:unit) : solver_state

// Push a context
val push (s:solver_state) : solver_state

// Pop a context: All facts added since the last push are removed
val pop (s:solver_state) : solver_state

// Get the current depth of the context stack:
// Useful in implementing snapshot and rollback, which are used in the IDE
// to restore the state of the solver to a previous point, rather than just
// popping the context one at a time
val depth (s:solver_state) : int

// Reset the state, so that the next flush will yield all the declarations
// that should be sent to a _fresh_ Z3 process to bring it to a state
// logicallly equivalent to the current solver state
val reset (_:option using_facts_from_setting) (s:solver_state) : solver_state

// Give the solver some declarations
val give (ds:list decl) (s:solver_state) : solver_state

// Start a query context: Queries are handled specially, since they trigger
// various kinds of filters. 
//
// This function pushes a context, and then adds roots to the solver state.
//
// * msg: A caption to be added to the SMT encoding for this query
//
// * roots: A list of query-specific declarations, e.g, an encoding of the local
//    binders of the query 
//
// * qry: The query itself: This is NOT given to the solver. Instead, (qry::roots) are 
//    registered in the solver state as the roots from which to scan for context pruning. 
//
val start_query (msg:string) (roots:list decl) (qry:decl) (s:solver_state) : solver_state

// Pops the context pushed at when starting a query
// Clears any registered roots for context pruning
val finish_query (msg:string) (s:solver_state) : solver_state

// Filters all declarations visible with an unsat core and returns the result
// Does not change the solver state
//
// Queries filtered with an unsat core are always sent to a fresh Z3 process, 
// and if they fail, the query falls back to a background process whose state is `s`.
// Filtering with an unsat core does not change the staet of s.
val filter_with_unsat_core (queryid:string) (_:U.unsat_core) (s:solver_state) : list decl

// Get all declarations to be given to the solver since the last flush
// and update the solver state.
val flush (s:solver_state) : list decl & solver_state

// If context_pruning_sim is set, this function returns the names of all declarations
// that would have been given to the solver if the context were pruned.
// This is useful for debugging whether context_pruning removed assumptions that are
// otherwise necessary for a proof.
val would_have_pruned (s:solver_state) : option (list string)