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
open FStarC.SMTEncoding.Env
open FStarC.Range

module S = FStarC.Syntax.Syntax

(* A single proof obligation: an atomic formula to be discharged, together
   with the error message and source range to report if it fails.  It is kept
   both in its encoded form, which is what we ask the solver about, and in its
   original form, which is what we show the user. *)
type goal = {
  goal_id     : int;
  goal_msg    : Errors.error_message;
  goal_range  : Range.t;
  goal_term   : term;
  goal_source : S.term;
}

(* An element of the proof context of a goal, for reporting. *)
type ctx_elt =
  | CVar   : S.bv -> ctx_elt              (* a universally quantified variable *)
  | CDef   : S.bv -> S.term -> ctx_elt    (* a let-bound variable *)
  | CHyp   : S.term -> ctx_elt            (* an assumption *)
  | CMatch : S.term -> S.pat -> ctx_elt   (* a scrutinee known to match a pattern *)

(* The structure of a verification condition, as a tree of goals sharing
   a context of declarations and hypotheses.  Emitting it to the solver
   sends each shared declaration/hypothesis exactly once, and asks a
   separate (check-sat) per leaf. *)
type goal_tree =
  | GTrivial : goal_tree
  | GLeaf    : goal -> goal_tree
  | GCtx     : list decl -> list ctx_elt -> goal_tree -> goal_tree
  | GBranch  : list goal_tree -> goal_tree

(* The goals of a tree, in the order in which they are emitted. *)
val goals_of : goal_tree -> ML (list goal)

(* The proof context of a given goal, outermost first: the variables of the
   enclosing universals, the left-hand sides of the enclosing implications,
   and the patterns of the enclosing match branches. *)
val goal_context : goal_tree -> goal -> ML (list ctx_elt)

(* Every declaration and assumption of the tree, ignoring scoping.  Used as
   the set of roots for context pruning. *)
val all_decls : goal_tree -> ML (list decl)

(* Traverse a verification condition, skolemizing universal quantifiers,
   turning the left-hand sides of implications into hypotheses, and encoding
   the leaves as individual goals. *)
val split_goals : option (unit -> ML string)  //when present, provides an alternate error message,
                                              //usually "could not check implicit argument"
               -> env_t
               -> q:S.term
               -> ML (goal_tree & decls_t)
