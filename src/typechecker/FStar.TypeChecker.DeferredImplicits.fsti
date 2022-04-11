(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Nikhil Swamy, ...
*)
//////////////////////////////////////////////////////////////////////////
//Refinement subtyping with higher-order unification
//with special treatment for higher-order patterns
//////////////////////////////////////////////////////////////////////////

module FStar.TypeChecker.DeferredImplicits
open FStar.Compiler.Effect
open FStar.Compiler.Effect
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common

val should_defer_uvar_to_user_tac : env -> ctx_uvar -> bool
val solve_deferred_to_tactic_goals: env -> guard_t -> guard_t
