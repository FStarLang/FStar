(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.Core.Binders

(* Binders in the core typechecker (see FStarC.TypeChecker.Core): the
   initial environment, pushing binders and hypotheses, and opening terms,
   comps, patterns and branches.

   Core opens binders deterministically: a binder is given the index next
   above the largest index in scope ([max_binder_index]), so that the same
   term opened in the same context is the same term, and its checks can be
   memoized. *)

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Core.Base
module Env = FStarC.TypeChecker.Env

(* The environment in which Core checks a term in [g]. *)
val initial_env (g:Env.env) : ML env

(*** Pushing binders *)

val push_binder (g:env) (b:binder) : ML env

val push_binders (g:env) (bs:binders) : ML env

(* A variable of sort [t], with a reserved name and index 0, for patterns
   and binders whose name does not matter. *)
val wild_bv (t:typ) (r:Range.t) : bv

(*** Opening *)

(* Open [bs], returning the substitution of the fresh variables for the
   bound ones. *)
val open_binders (g:env) (bs:binders) : ML (env & binders & subst_t)

val open_term (g:env) (b:binder) (t:term) : ML (env & binder & term)

val open_term_binders (g:env) (bs:binders) (t:term) : ML (env & binders & term)

val open_comp (g:env) (b:binder) (c:comp) : ML (env & binder & comp)

val open_comp_binders (g:env) (bs:binders) (c:comp) : ML (env & binders & comp)

(* The binders of the names of a nest of recursive definitions, at their
   annotated types. *)
val letrec_binders (lbs:list letbinding) : ML binders

(* Open the variables of the pattern of a branch. *)
val open_branch (g:env) (br:branch) : ML (env & branch)

(* Open two branches with equal patterns with the same variables. *)
val open_branches_eq_pat (g:env) (br0 br1:branch) : ML (env & branch & branch)

(* The function [fun (x:a) -> f x], for a fresh [x]. *)
val abs (g:env) (a:typ) (f: binder -> term) : ML term

(*** Hypotheses *)

(* Push the hypothesis [h], as an anonymous binder of sort [h]. *)
val push_hypothesis (g:env) (h:term) : ML env

(* Push the hypothesis under which a branch is taken (see
   [Core.Guard.branch_conditions]), unless it is trivial. *)
val push_branch_hypothesis (g:env) (hyp:typ) : ML env
