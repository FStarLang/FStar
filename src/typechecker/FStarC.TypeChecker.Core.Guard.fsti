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
module FStarC.TypeChecker.Core.Guard

(* Guards in the core typechecker (see FStarC.TypeChecker.Core): emitting
   them (through the guard cache, see [Core.Cache]), and transforming the
   guard of a computation as it goes out of the scope of binders,
   hypotheses and definitions, or to label it for error reporting. The
   transformers take the guard of a computation (with
   [Core.Monad.with_guard]) and emit the transformed guard with
   [reemit_guard]. *)

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Core.Base
open FStarC.TypeChecker.Core.Monad
module R = FStarC.Range

(*** Formulas *)

(* [forall (xs:us). t], as [Env.close_guard] (dropping quantifiers over
   unused binders of type [unit]). *)
val mk_forall_l (us:universes) (xs:binders) (t:term) : ML term

(* [forall x. t == x ==> g], for [x] of universe [u] defined as [t]. *)
val close_with_definition (x:binder) (u:universe) (t:term) (g:typ) : ML typ

(*** Emitting guards *)

(* Emit [guard], unless it was emitted in a context included in that of
   [g]. *)
val guard (g:env) (guard:typ) : result unit

(* Emit [guard], a transformation of the guard of a sub-computation,
   bypassing the cache. *)
val reemit_guard (g:env) (guard:typ) : result unit

(* Where no guard is allowed: [f], or else [f] allowing a guard, provided
   that guard simplifies to [True] ([VCUtil.simplify_vc]), as Rel's
   [teq_nosmt] discharges its own; e.g. [hide (reveal x) == x], which only a
   primitive step decides. If both fail, [f]'s error. Where guards are
   allowed, this is [f]. *)
val guard_if_trivial (g:env) (f:result unit) : result unit

(* The guard [phi] about the witness of a refinement subtyping, whose
   subterms have the facts [fs], which are assumed. *)
val witness_guard (g:env) (fs:Thunk.t (list term)) (phi:typ) : ML (result unit)

(* Either of two checks suffices: if both have guards, their disjunction is
   the guard. *)
val either_guard (f1 f2: unit -> ML (result unit)) : result unit

(*** Closing guards *)

(* Close the guard of [f] over [xs], of universes [us], which are in scope
   in [f] but not in [initial_env]. *)
val with_binders (#a:Type) (initial_env:env) (xs:binders) (us:universes) (f:result a)
  : result a

(* As [with_binders] for one binder; if its sort is a refinement
   [y:t{phi}], quantifies over [t] and assumes [phi]. *)
val with_binder_unrefined (#a:Type) (initial_env:env) (x:binder) (u:universe) (f:result a)
  : ML (result a)

(* Weaken the guard of [f] with a branch hypothesis (see
   [branch_conditions]), unless it is trivial. *)
val weaken_branch (#a:Type) (initial_env:env) (hyp:typ) (f:result a) : ML (result a)

(* Weaken the guard of [g] with [p], unless it is trivial. *)
val weaken_with_guard_formula (#a:Type) (env:env) (p:FStarC.TypeChecker.CommonBase.guard_formula) (g:result a)
  : ML (result a)

(*** Labeling guards *)

(* Label the guard of [f] with [msg], at [r], for the SMT solver to report
   when it cannot prove it. The message is only computed if there is a
   guard. *)
val label_guard (#a:Type) (g:env) (r:R.t) (msg:unit -> ML Errors.error_message) (f:result a)
  : result a

(* Label the guard of [f] as a postcondition, at [at]. *)
val label_postcondition (#a:Type) (g:env) (at:term) (f:result a) : result a

(* Label the guard of [f], which proves that the type [t0] of [e] is a
   subtype of [t1], as TcTerm does. *)
val label_subtyping (#a:Type) (g:env) (e:term) (t0 t1:typ) (f:result a) : ML (result a)

(* [e <: t by tac]: the guard of [f], which checks [e] against [t], is left
   to [tac], even when trivial. *)
val with_ascription_tactic (#a:Type) (g:env) (tac:option term) (f:unit -> ML (result a))
  : ML (result a)

(*** Branches *)

(* The conditions of a branch, as TcTerm has them: given the path
   condition of the branch, its branch condition (if its pattern is
   refutable) and the equation [eq] of the scrutinee with its pattern, the
   hypothesis under which the branch is taken, that and [eq], and the path
   condition of the next branch. *)
val branch_conditions (path_condition:typ) (branch_condition:option term) (eq:typ)
  : ML (typ & typ & typ)

(* The obligation that no branch is missing, given the path condition after
   the last branch, if not trivial. *)
val exhaustiveness_obligation (r:R.t) (path_condition:typ) : ML (option typ)
