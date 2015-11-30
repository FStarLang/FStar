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

module FStar.TypeChecker.Util

open FStar
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.TypeChecker.Rel
open FStar.Syntax.Syntax
open FStar.Ident

//error report
val report: env -> list<string> -> unit

//calling the SMT solver
val discharge_guard: env -> guard_t -> unit

//unification variables
val new_uvar : env -> typ -> typ
val as_uvar : typ -> uvar
val new_implicit_var : env -> typ -> (typ * (uvar * Range.range))
val check_uvars: Range.range -> typ -> unit

//extracting annotations from a term
val force_sort: syntax<'a,'b> -> 'b
val sorts_of_args: args -> list<(term' * aqual)>
val extract_lb_annotation: env -> typ -> term -> (term * typ * bool)

//pattern utilities
val pat_as_exps: bool -> env -> pat -> (list<Env.binding> * list<term> * pat)
val decorate_pattern: env -> pat -> list<term> -> pat
val decorated_pattern_as_term: pat -> list<bv> * term

//instantiation and generalization
val maybe_instantiate : env -> term -> typ -> (term * typ * implicits)
val generalize: bool -> env -> list<(lbname*term*comp)> -> list<(lbname*term*comp)>

//operations on computation types
(* most operations on computations are lazy *)
type lcomp_with_binder = option<Env.binding> * lcomp
val lcomp_of_comp: comp -> lcomp
val subst_lcomp: subst -> lcomp -> lcomp
val is_pure_effect: env -> lident -> bool
val is_pure_or_ghost_effect: env -> lident -> bool
val return_value: env -> typ -> term -> comp
val bind: env -> option<term> -> lcomp -> lcomp_with_binder -> lcomp
val bind_cases: env -> typ -> list<(typ * lcomp)> -> lcomp
val ite: env -> formula -> lcomp -> lcomp -> lcomp
val weaken_result_typ: env -> term -> lcomp -> typ -> term * lcomp * guard_t
val strengthen_precondition: option<(unit -> string)> -> env -> term -> lcomp -> guard_t -> lcomp*guard_t
val weaken_guard: guard_formula -> guard_formula -> guard_formula
val weaken_precondition: env -> lcomp -> guard_formula -> lcomp
val maybe_assume_result_eq_pure_term: env -> term -> lcomp -> lcomp
val close_comp: env -> list<binding> -> lcomp -> lcomp
val refresh_comp_label: env -> bool -> lcomp -> lcomp
val pure_or_ghost_pre_and_post: env -> comp -> (option<typ> * typ)
val check_comp: env -> term -> comp -> comp -> term * comp * guard_t

//checking that e:t is convertible to t'
val check_and_ascribe : env -> term -> typ -> typ -> term * Rel.guard_t
val check_top_level: env -> guard_t -> lcomp -> bool*comp

//misc.
val label: string -> Range.range -> typ -> typ
val label_guard: string -> Range.range -> guard_formula -> guard_formula
val short_circuit: term -> args -> guard_formula
val mk_basic_dtuple_type: env -> int -> typ

