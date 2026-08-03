(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStarC.SMTEncoding.ErrorReporting
open FStarC.Effect
open FStarC
open FStarC.BaseTypes
open FStarC.SMTEncoding.Term
open FStarC.SMTEncoding.Util
open FStarC.SMTEncoding
open FStarC.Range

(* A single proof obligation: an atomic formula to be discharged, together
   with the error message and source range to report if it fails. *)
type goal = {
  goal_id    : int;
  goal_msg   : Errors.error_message;
  goal_range : Range.t;
  goal_term  : term;
}

(* The structure of a verification condition, as a tree of goals sharing
   a context of declarations and hypotheses.  Emitting it to the solver
   sends each shared declaration/hypothesis exactly once, and asks a
   separate (check-sat) per leaf. *)
type goal_tree =
  | GTrivial : goal_tree
  | GLeaf    : goal -> goal_tree
  | GCtx     : list decl -> goal_tree -> goal_tree
  | GBranch  : list goal_tree -> goal_tree

(* Traverse an encoded verification condition, skolemizing universal
   quantifiers, turning the left-hand sides of implications into
   hypotheses, and collecting the leaves as individual goals. *)
(* The goals of a tree, in the order in which they are emitted. *)
val goals_of : goal_tree -> ML (list goal)

val split_goals : option (unit -> ML string) -> range -> q:term -> ML goal_tree
