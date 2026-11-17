(*
   Copyright 2008-2025 Microsoft Research

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
(* Typeclass resolution.

   This only elaborates: it finds an instance term for a goal, and computes no
   proof obligations.  Each part of the solution that is not well-typed by
   construction (e.g. a [()] for a [squash] argument of an instance) is the
   solution of a fresh, strictly-checked uvar among the returned implicits, so
   that checking those implicits emits the proof obligations.

   Results are cached in the [tc_cache] of the [tc_scope] of the goal.  The
   key is the goal with its functional dependencies replaced by [_]: the search
   itself never looks at them, so the instance found only depends on the key. *)
module FStarC.TypeChecker.TcResolve

open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env

(* The class of a type, if it is a class constraint, possibly under Tot
   arrows and refinements, and after unfolding [unfold] definitions. *)
val class_of_typ (env:env) (t:typ) : ML (option FStarC.Ident.lident)

(* Solve a typeclass goal in [env.gamma] with the local instances of [scope].
   Returns the instance and the implicits it introduced, or raises an error. *)
val resolve (env:env) (scope:tc_scope) (goal:typ) (rng:FStarC.Range.t) : ML (term & list implicit)
