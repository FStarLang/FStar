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
(* The termination goals of recursive definitions, shared by [TcTerm] and
   Core. *)
module FStarC.TypeChecker.Termination

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env

(* Is [t] the type of a precondition, i.e. a [squash]? *)
val is_squash_typ : env -> typ -> ML bool

(* Given the letrecs being checked (env.letrecs), the actual binders of a
   recursive function and its expected computation type, return the types of
   the recursive names, refined for termination checking.

   The refinements use the universe-polymorphic [precedes] and [eq3]: with
   [inst_univs], they are instantiated with fresh universe unification
   variables, for the caller to solve; otherwise they are left
   uninstantiated, for the elaborator. *)
val guard_letrecs : inst_univs:bool -> env -> binders -> comp -> ML (list (lbname & typ & univ_names))
