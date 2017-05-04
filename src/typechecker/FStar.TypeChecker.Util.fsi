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
open FStar.All

open FStar
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.TypeChecker.Common

//error report
val report: env -> list<string> -> unit

//unification variables
val new_uvar : env -> typ -> typ
val as_uvar  : typ -> uvar
val new_implicit_var : string -> Range.range -> env -> typ -> (term * list<(uvar * Range.range)> * guard_t)
val check_uvars: Range.range -> typ -> unit

//extracting annotations from a term
val extract_let_rec_annotation: env -> letbinding -> (univ_names * typ * bool)

//pattern utilities
val pat_as_exps: bool -> env -> pat -> (list<bv> * list<term> * pat)
val decorate_pattern: env -> pat -> list<term> -> pat
val decorated_pattern_as_term: pat -> list<bv> * term

//instantiation and generalization
val maybe_instantiate : env -> term -> typ -> (term * typ * guard_t)
val generalize: env -> list<(lbname*term*comp)> -> list<(lbname*univ_names*term*comp)>
val generalize_universes: env -> term -> tscheme

//operations on computation types
(* most operations on computations are lazy *)
type lcomp_with_binder = option<bv> * lcomp
val subst_lcomp: subst_t -> lcomp -> lcomp
val is_pure_effect: env -> lident -> bool
val is_pure_or_ghost_effect: env -> lident -> bool
val return_value: env -> typ -> term -> comp
val bind: Range.range -> env -> option<term> -> lcomp -> lcomp_with_binder -> lcomp
val bind_cases: env -> typ -> list<(typ * lcomp)> -> lcomp
val ite: env -> formula -> lcomp -> lcomp -> lcomp
val weaken_result_typ: env -> term -> lcomp -> typ -> term * lcomp * guard_t
val strengthen_precondition: (option<(unit -> string)> -> env -> term -> lcomp -> guard_t -> lcomp*guard_t)
val weaken_guard: guard_formula -> guard_formula -> guard_formula
val weaken_precondition: env -> lcomp -> guard_formula -> lcomp
val maybe_assume_result_eq_pure_term: env -> term -> lcomp -> lcomp
val close_comp: env -> list<bv> -> lcomp -> lcomp
val pure_or_ghost_pre_and_post: env -> comp -> (option<typ> * typ)
val check_comp: env -> term -> comp -> comp -> term * comp * guard_t

//checking that e:t is convertible to t'
val check_and_ascribe : env -> term -> typ -> typ -> term * guard_t
val check_top_level: env -> guard_t -> lcomp -> bool*comp
val maybe_coerce_bool_to_type: env -> term -> lcomp -> typ -> term * lcomp

//misc.
val label: string -> Range.range -> typ -> typ
val label_guard: Range.range -> string -> guard_t -> guard_t
val short_circuit: term -> args -> guard_formula
val short_circuit_head: term -> bool
val maybe_add_implicit_binders: env -> binders -> binders
val fvar_const: env -> lident -> term
val mk_toplevel_definition: env -> lident -> term -> sigelt * term
val reify_body: env -> term -> term
val reify_body_with_arg: env -> term -> arg -> term
val remove_reify: term -> term

//decorating terms with monadic operators
val maybe_lift: env -> term -> lident -> lident -> typ -> term
val maybe_monadic: env -> term -> lident -> typ -> term

//qualifiers
val check_sigelt_quals: env -> sigelt -> unit

//elaborate discriminator and projectors
val mk_data_operations : list<qualifier> -> env -> list<sigelt> -> sigelt -> list<sigelt>
