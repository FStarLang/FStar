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
open FStarC
open FStarC.SMTEncoding.Term

(* Each element of the outer list is a disjunct; an assumption is triggered when
   all the names of some disjunct have been reached. *)
type triggers = list (list string)

(** Summaries.

  Running the pruning algorithm only needs a small amount of information about
  each declaration: essentially just names. A [decl_summary] captures exactly
  that information, and is small enough to be stored in a .checked file and
  loaded eagerly, while the declarations themselves are only deserialized if
  and when the pruning algorithm decides to retain them. *)

(* How an assumption participates in the pruning graph. This is derived from
   the shape of the assumption's term; see [summarize_decls]. *)
type asum_kind =
  (* The assumption waits on these triggers; each inner list is a disjunct. *)
  | Sum_triggers of triggers
  (* The assumption has no usable trigger and is always retained.
     The boolean says whether it is also an extra root of the scan. *)
  | Sum_ambient of bool
  (* The assumption is vacuous and never retained. *)
  | Sum_drop

type assumption_summary = {
  asum_name : string;
  asum_free_names : list string;
  (* [assumption_caption = Some "pretyping"]; those are retained only
     under --ext pretyping_axioms *)
  asum_pretyping : bool;
  asum_kind : asum_kind;
}

type decl_summary =
  | Sum_assume of assumption_summary
  | Sum_declfun of string
  (* macro name, and the free names of its body *)
  | Sum_definefun of string & list string
  | Sum_retain of list string
  (* Caption and EmptyLine: no effect on the solver state *)
  | Sum_ignored
  (* Anything else: has to be given to the solver eagerly *)
  | Sum_other of decl

(* The main abstract type of this module, representing the set of all assumptions *)
val pruning_state  : Type0

val init : pruning_state

(* The summary of one [decls_elt]: its hash-consing key and assumption names
   (which is all [recover_caching_and_update_env] needs), plus the summaries of
   the declarations it contains. *)
type elt_summary = {
  elts_key : option string;
  elts_a_names : list string;
  elts_sums : list decl_summary
}

(* Summarize a list of declarations, flattening [Module] nodes.
   The result has exactly one entry per (flattened) declaration. *)
val summarize_decls (ds:list decl) : ML (list decl_summary)

(* The eagerly-loaded index of a module's SMT encoding *)
val summarize_elts (ds:decls_t) : ML (list elt_summary)

(* Add summarized declarations to the pruning state. [resolve] maps the name of
   a declaration (see [Sum_assume], [Sum_declfun], [Sum_definefun]) to the
   declaration itself; it is called only for declarations that survive pruning. *)
val add_summaries (sums:list decl_summary)
                  (resolve:string -> ML (option decl))
                  (p:pruning_state)
: ML pruning_state

(* Adding assumptions to the pruning state *)
val add_decls (ds:list decl) (p:pruning_state) : ML pruning_state

(* Pruning the state to only include the assumptions that are reachable from the roots *)
val prune (p:pruning_state) (roots:list decl) : ML (list decl)
