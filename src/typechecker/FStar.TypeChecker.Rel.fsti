﻿(*
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

module FStar.TypeChecker.Rel
open FStar.Pervasives
open FStar.Compiler.Effect

open FStar
open FStar.Compiler
open FStar.Compiler.Util
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.TypeChecker.Common
open FStar.Compiler.Range

type implicit_checking_status =
  | Implicit_unresolved
  | Implicit_checking_defers_univ_constraint
  | Implicit_has_typing_guard of term * typ

type tagged_implicits = list (implicit * implicit_checking_status)

val is_base_type : env -> typ -> bool
val prob_to_string: env -> prob -> string
val flex_prob_closing         : env -> binders -> prob -> bool
//val close_guard_univs         : universes -> binders -> guard_t -> guard_t
//val close_guard               : env -> binders -> guard_t -> guard_t
//val apply_guard               : guard_t -> term -> guard_t
//val map_guard                 : guard_t -> (term -> term) -> guard_t
//val trivial_guard             : guard_t
//val is_trivial                : guard_t -> bool
//val is_trivial_guard_formula  : guard_t -> bool
//val conj_guard                : guard_t -> guard_t -> guard_t
//val abstract_guard            : binder -> guard_t -> guard_t
//val abstract_guard_n          : list binder> -> guard_t - guard_t
//val imp_guard                 : guard_t -> guard_t -> guard_t
//val guard_of_guard_formula    : guard_formula -> guard_t
//val guard_form                : guard_t -> guard_formula
val guard_to_string           : env -> guard_t -> string
val simplify_guard            : env -> guard_t -> guard_t
val solve_deferred_constraints: env -> guard_t -> guard_t
val solve_non_tactic_deferred_constraints: maybe_defer_flex_flex:bool -> env -> guard_t -> guard_t
val discharge_guard_no_smt    : env -> guard_t -> guard_t
val discharge_guard           : env -> guard_t -> guard_t
val force_trivial_guard       : env -> guard_t -> unit
val is_implicit_resolved      : env -> Env.implicit -> bool
val check_implicit_solution_for_tac : env -> Env.implicit -> option (term * typ)
val resolve_implicits         : env -> guard_t -> guard_t
val resolve_implicits_tac     : env -> guard_t -> tagged_implicits
val base_and_refinement_maybe_delta : bool -> env -> term -> term * option (bv * term)
val base_and_refinement       : env -> term -> term * option (bv * term)

val unrefine   : env -> typ -> typ
val try_teq    : bool -> env -> typ -> typ -> option guard_t
val teq        : env -> typ -> typ -> guard_t
val get_teq_predicate : env -> typ -> typ -> option guard_t
val teq_force  : env -> typ -> typ -> unit
val teq_nosmt        : env -> typ -> typ -> option guard_t
val teq_nosmt_force  : env -> typ -> typ -> bool
val layered_effect_teq : env -> typ -> typ -> reason:option string -> guard_t
val get_subtyping_predicate: env -> typ -> typ -> option guard_t
val get_subtyping_prop: env -> typ -> typ -> option guard_t
val subtype_nosmt       : env -> typ -> typ -> option guard_t
val subtype_nosmt_force : env -> typ -> typ -> bool
val sub_comp   : env -> comp -> comp -> option guard_t
val eq_comp : env -> comp -> comp -> option guard_t

val universe_inequality : universe -> universe -> guard_t

val subtype_fail: env -> term -> typ -> typ -> unit
val print_pending_implicits: guard_t -> string
