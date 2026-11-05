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
(* Relating two types, deciding with FStarC.TypeChecker.Core.

   Rel is an elaborator: it solves unification variables, but it is not
   trusted to decide whether two types are related. Where a relation decides
   something that is not re-checked by Core -- e.g., whether a tactic's
   [exact] solves a goal, or a check on an inductive type -- it goes through
   the functions here: Rel solves the unification variables of the two
   types, in a transaction, and Core then decides the relation between the
   types so instantiated. If Core rejects it, the transaction is rolled back,
   undoing Rel's solution.

   If [env.admit] is set, nothing is proven, and Rel's answer is taken as it
   is: the terms elaborated in such an environment are re-checked by Core
   (see [CoreCheck]), unless verification is disabled. *)
module FStarC.TypeChecker.CoreRel

open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env

(* [try_teq guard_ok env t1 t2]: whether [t1] and [t2] are equal. If
   [guard_ok], the result's logical guard is Core's proof obligation for
   that, if any; otherwise, they must be equal without one (or with one
   that simplifies to [True]), and the result's logical guard is trivial.
   The result carries the implicits of Rel's solution. *)
val try_teq (guard_ok:bool) (env:env) (t1 t2:typ) : ML (option guard_t)

(* As [try_teq], for the subtyping [t1 <: t2]. *)
val try_subtype (guard_ok:bool) (env:env) (t1 t2:typ) : ML (option guard_t)

(* Whether [t1] and [t2] are equal without a proof obligation, solving the
   implicits of Rel's solution (as [Rel.teq_nosmt_force]). *)
val teq_nosmt_force (env:env) (t1 t2:typ) : ML bool

(* As [teq_nosmt_force], for the subtyping [t1 <: t2]. *)
val subtype_nosmt_force (env:env) (t1 t2:typ) : ML bool
