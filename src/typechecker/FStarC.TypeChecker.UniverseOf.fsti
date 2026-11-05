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
(* The types of constants, and the universes of well-typed types, computed
   mostly syntactically. Shared by [TcTerm] and Core: the few cases that
   cannot be computed syntactically are delegated to [hooks], which [TcTerm]
   implements with the elaborator, while Core implements them by failing
   (and then computes the universe itself). *)
module FStarC.TypeChecker.UniverseOf

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env

type hooks = {
  (* The type of the head of an application that is not typed
     syntactically, e.g. a [let]. *)
  type_of_head : env -> term -> ML typ;
  (* The universe of [e], whose type [t] is not [Type u], even after
     unfolding. *)
  level_of_non_type : env -> term -> typ -> ML universe;
}

(* The type of a constant, at range [r]. *)
val tc_constant : env -> Range.t -> sconst -> ML typ

val level_of_type_fail : env -> term -> string -> ML 'a

(* The universe of [e], of type [t]. *)
val level_of_type : hooks -> env -> term -> typ -> ML universe

(* The type of applying a term of type [t_hd] to [args], assuming it is
   well-typed. *)
val apply_well_typed : env -> typ -> args -> ML (option typ)

(* [Type u], where [u] is the universe of the type [e], assumed to be
   well-typed. *)
val universe_of_aux : hooks -> env -> term -> ML term

(* The universe of the type [e], assumed to be well-typed. *)
val universe_of : hooks -> env -> term -> ML universe

(* Hooks that fail. *)
val no_hooks : hooks
