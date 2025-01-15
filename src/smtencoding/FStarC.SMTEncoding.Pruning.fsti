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
module FStarC.SMTEncoding.Pruning
(**
  This module provides support for the '--ext context_pruning' feature.

  It maintains a `pruning_state`, a collection of SMT assumptions.

  Given a set of root SMT declarations, it computes the set of assumptions
  "reacahable" from those roots, i.e., computing a pruning of the state to only
  include the facts that are relevant to the roots.

  The way this works, roughly, is as following:

  The set of all reachable symbols is initially all the free variables of the
  roots and the pruned set is empty.

  A given assumption in the context is a quantified fact of the form:

    A: forall x1...xn. {:pattern (p1; ...; pk)} Q

  This assumption A is reachable if all the free variables of the patterns
  (p1;...;pk) are reachable. If so, then the free variables of Q are added to
  the set of reachable symbols, A is added to the pruned set, and the process is
  repeated until fixpoint, returning the pruned set.

  Enhancements to this basic idea support 
    - quantifiers with disjunctive patterns
    - top-level non-quantified facts
    - macros
    - and some features that are specific to F*'s SMT encoding

  Thanks to Chris Hawblitzel and Guido Martínez for design and discussions.
*)
open FStarC.Effect
open FStar open FStarC
open FStarC
open FStarC.SMTEncoding.Term

(* The main abstract type of this module, representing the set of all assumptions *)
val pruning_state  : Type0

val init : pruning_state

(* Adding assumptions to the pruning state *)
val add_decls (ds:list decl) (p:pruning_state) : pruning_state

(* Pruning the state to only include the assumptions that are reachable from the roots *)
val prune (p:pruning_state) (roots:list decl) : list decl