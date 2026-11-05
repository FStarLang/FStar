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
(* Definitions shared across the typechecker, including Core, that do not
   concern unification problems. [FStarC.TypeChecker.Common] includes this
   module. *)
module FStarC.TypeChecker.CommonBase

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Class.Show

type guard_formula =
  | Trivial
  | NonTrivial of formula

instance val showable_guard_formula : showable guard_formula

(* [by_tactic tac f] *)
val mk_by_tactic : term -> term -> ML term

val delta_depth_greater_than : delta_depth -> delta_depth -> bool
val decr_delta_depth : delta_depth -> option delta_depth

(* Whether a binder with positivity qualifier [p0] may be used where one with
   [p1] is expected: they are equal or, when [subtyping], [p0] is stronger. *)
val check_positivity_qual (subtyping:bool) (p0 p1:option positivity_qualifier)
  : bool
