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
#light "off"
module FStar.TypeChecker.Rel
open FStar.ST
open FStar.All

open FStar
open FStar.Util
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.TypeChecker.Common

val new_uvar: Range.range -> binders -> typ -> typ * typ

val close_guard_univs         : universes -> binders -> guard_t -> guard_t
val close_guard               : env -> binders -> guard_t -> guard_t
val apply_guard               : guard_t -> term -> guard_t
val map_guard                 : guard_t -> (term -> term) -> guard_t
val trivial_guard             : guard_t
val is_trivial                : guard_t -> bool
val conj_guard                : guard_t -> guard_t -> guard_t
val abstract_guard            : binder -> guard_t -> guard_t
val abstract_guard_n          : list<binder> -> guard_t -> guard_t
val imp_guard                 : guard_t -> guard_t -> guard_t
val guard_of_guard_formula    : guard_formula -> guard_t
val guard_form                : guard_t -> guard_formula
val guard_to_string           : env -> guard_t -> string
val simplify_guard            : env -> guard_t -> guard_t
val solve_deferred_constraints: env -> guard_t -> guard_t
val discharge_guard_no_smt    : env -> guard_t -> guard_t
val discharge_guard           : env -> guard_t -> guard_t
val force_trivial_guard       : env -> guard_t -> unit
val resolve_implicits         : guard_t -> guard_t
val resolve_implicits_tac     : guard_t -> guard_t
val guard_unbound_vars        : env -> guard_t -> set<bv>
val check_term                : string -> env -> term -> unit
val check_guard               : string -> env -> guard_t -> unit

val unrefine   : env -> typ -> typ
val try_teq    : bool -> env -> typ -> typ -> option<guard_t>
val teq        : env -> typ -> typ -> guard_t
val teq_nosmt  : env -> typ -> typ -> bool
val try_subtype: env -> typ -> typ -> option<guard_t>
val try_subtype': env -> typ -> typ -> bool -> option<guard_t>
val sub_comp   : env -> comp -> comp -> option<guard_t>

val universe_inequality : universe -> universe -> guard_t

val subtype_fail: env -> term -> typ -> typ -> unit
val print_pending_implicits: guard_t -> string
