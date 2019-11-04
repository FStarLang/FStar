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
open FStar.ST
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
val new_implicit_var : string -> Range.range -> env -> typ -> (term * list<(ctx_uvar * Range.range)> * guard_t)
val check_uvars: Range.range -> typ -> unit

//caller can set the boolean to true if they want to solve the deferred constraints involving this binder now (best case)
val close_guard_implicits: env -> bool -> binders -> guard_t -> guard_t

//extracting annotations from a term
val extract_let_rec_annotation: env -> letbinding -> univ_names * typ * bool

//pattern utilities
//val decorate_pattern: env -> pat -> term -> pat
val decorated_pattern_as_term: pat -> list<bv> * term

//instantiation and generalization
val maybe_instantiate : env -> term -> typ -> (term * typ * guard_t)
val generalize: env -> bool -> list<(lbname*term*comp)> -> list<(lbname*univ_names*term*comp*list<binder>)>
val generalize_universes: env -> term -> tscheme

//operations on computation types
(* most operations on computations are lazy *)
type lcomp_with_binder = option<bv> * lcomp
val lcomp_univ_opt: lcomp -> (option<universe> * guard_t)
val is_pure_effect: env -> lident -> bool
val is_pure_or_ghost_effect: env -> lident -> bool
val should_not_inline_lc: lcomp -> bool
val should_return: env -> option<term> -> lcomp -> bool
val return_value: env -> option<universe> -> typ -> term -> comp
val bind: Range.range -> env -> option<term> -> lcomp -> lcomp_with_binder -> lcomp
val maybe_return_e2_and_bind: Range.range -> env -> option<term> -> lcomp -> e2:term -> lcomp_with_binder -> lcomp
val bind_cases: env -> typ -> list<(typ * lident * list<cflag> * (bool -> lcomp))> -> lcomp
val weaken_result_typ: env -> term -> lcomp -> typ -> term * lcomp * guard_t
val strengthen_precondition: (option<(unit -> string)> -> env -> term -> lcomp -> guard_t -> lcomp*guard_t)
val weaken_guard: guard_formula -> guard_formula -> guard_formula
val weaken_precondition: env -> lcomp -> guard_formula -> lcomp
val maybe_assume_result_eq_pure_term: env -> term -> lcomp -> lcomp
val close_wp_lcomp: env -> list<bv> -> lcomp -> lcomp
val close_layered_lcomp: env -> list<bv> -> list<term> -> lcomp -> lcomp
val pure_or_ghost_pre_and_post: env -> comp -> (option<typ> * typ)
val check_comp: env -> term -> comp -> comp -> term * comp * guard_t
val universe_of_comp: env -> universe -> comp -> universe
(*
 * return value: formula for input comp to have trivial wp * guard for that formula
 *)
val check_trivial_precondition : env -> comp -> (comp_typ * formula * guard_t)

//checking that e:t is convertible to t'
val check_and_ascribe : env -> term -> lcomp -> typ -> term * lcomp * guard_t
val check_top_level: env -> guard_t -> lcomp -> bool*comp

val maybe_coerce_lc : env -> term -> lcomp -> typ -> term * lcomp
val coerce_views    : env -> term -> lcomp -> option<(term * lcomp)>

//misc.
val label: string -> Range.range -> typ -> typ
val label_guard: Range.range -> string -> guard_t -> guard_t
val short_circuit: term -> args -> guard_formula
val short_circuit_head: term -> bool
val maybe_add_implicit_binders: env -> binders -> binders
val fvar_const: env -> lident -> term
val mk_toplevel_definition: env -> lident -> term -> sigelt * term
val reify_body: env -> steps -> term -> term
val reify_body_with_arg: env -> steps -> term -> arg -> term
val remove_reify: term -> term

//decorating terms with monadic operators
val maybe_lift: env -> term -> lident -> lident -> typ -> term
val maybe_monadic: env -> term -> lident -> typ -> term

//qualifiers
val check_sigelt_quals: env -> sigelt -> unit

val must_erase_for_extraction: env -> term -> bool

//layered effect utilities

(*
 * This function returns ed.repr<u> a ?u1 ... ?un (note that u must be the universe of a)
 *   where ?u1 ... ?un are unification variables, one for each index of the layered effect
 *
 * The unification variables are resolved in the input env
 *)
val fresh_effect_repr: env -> Range.range -> lident -> signature:tscheme -> repr:option<tscheme> -> u:universe -> a:term -> term * guard_t

(*
 * A wrapper over fresh_layered_effect_repr that looks up signature and repr from env
 *
 * If the effect does not have a repr (e.g. primitive effects), then we return a `unit -> M a ?u` term
 *)
val fresh_effect_repr_en: env -> Range.range -> lident -> universe -> term -> term * guard_t

(*
 * Return binders for the layered effect indices with signature
 * In the binder types, a is substituted with a_tm (u is universe of a)
 *)
val layered_effect_indices_as_binders:env -> Range.range -> eff_name:lident -> signature:tscheme -> u:universe -> a_tm:term -> binders

val get_mlift_for_subeff : env -> sub_eff -> Env.mlift

val get_field_projector_name : env -> datacon:lident -> index:int -> lident
