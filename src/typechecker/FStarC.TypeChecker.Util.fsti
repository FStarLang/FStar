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

module FStarC.TypeChecker.Util
open FStarC.Effect

open FStarC
open FStarC.TypeChecker
open FStarC.Syntax
open FStarC.TypeChecker.Env
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.TypeChecker.Common

type lcomp_with_binder = option bv & lcomp

//unification variables
val new_implicit_var : string -> Range.t -> env -> typ -> unrefine:bool -> ML (term & (ctx_uvar & Range.t) & guard_t)

//caller can set the boolean to true if they want to solve the deferred constraints involving this binder now (best case)
val close_guard_implicits: env -> bool -> binders -> guard_t -> ML guard_t

val check_uvars: Range.t -> typ -> ML unit

//extracting annotations from a term
val extract_let_rec_annotation: env -> letbinding -> ML (univ_names & typ & term & bool)

//pattern utilities
val decorated_pattern_as_term: pat -> ML (list bv & term)

//operations on computation types
val lcomp_univ_opt: lcomp -> ML (option universe & guard_t)

//misc.
val label: list Pprint.document -> Range.t -> typ -> ML typ
val label_guard: Range.t -> list Pprint.document -> guard_t -> ML guard_t

val is_pure_effect: env -> lident -> ML bool
val is_pure_or_ghost_effect: env -> lident -> ML bool

val close_wp_lcomp: env -> list bv -> lcomp -> ML lcomp
val close_layered_lcomp_with_combinator: env -> list bv -> lcomp -> ML lcomp
val close_layered_lcomp_with_substitutions: env -> list bv -> list term -> lcomp -> ML lcomp

val should_not_inline_lc: lcomp -> ML bool

val weaken_precondition: env -> lcomp -> guard_formula -> ML lcomp

val strengthen_precondition: option (unit -> ML (list Pprint.document)) -> env -> term -> lcomp -> guard_t -> ML (lcomp & guard_t)

val bind: Range.t -> is_let_binding:bool -> env -> option term -> lcomp -> lcomp_with_binder -> ML lcomp

val weaken_guard: guard_formula -> guard_formula -> ML guard_formula

val maybe_assume_result_eq_pure_term: env -> term -> lcomp -> ML lcomp

val maybe_return_e2_and_bind: Range.t -> is_let_binding:bool -> env -> option term -> lcomp -> e2:term -> lcomp_with_binder -> ML lcomp

val fvar_env: env -> lident -> ML term

(*
 * When typechecking a match term, typechecking each branch returns
 *   a branch condition
 *
 * E.g. match e with | C -> ... | D -> ...
 *   the two branch conditions would be (is_C e) and (is_D e)
 *
 * This function builds a list of formulas that are the negation of
 *   all the previous branches
 *
 * In the example, neg_branch_conds would be:
 *   [True; not (is_C e); not (is_C e) /\ not (is_D e)]
 *   thus, the length of the list is one more than lcases
 *
 * The return value is then ([True; not (is_C e)], not (is_C e) /\ not (is_D e))
 *
 * (The last element of the list becomes the branch condition for the
     unreachable branch to check for pattern exhaustiveness)
 *)
val get_neg_branch_conds: list formula -> ML (list formula & formula)

//the bv is the scrutinee binder, that bind_cases uses to close the guard (from lifting the computations)
val bind_cases: env -> typ -> list (typ & lident & list cflag & (bool -> ML lcomp)) -> bv -> ML lcomp

//
// Setting the boolean flag to true, clients may say if they want to use equality
//   instead of subtyping
//
val check_comp: env -> use_eq:bool -> term -> comp -> comp -> ML (term & comp & guard_t)

val universe_of_comp: env -> universe -> comp -> ML universe

(*
 * return value: formula for input comp to have trivial wp * guard for that formula
 *)
val check_trivial_precondition_wp : env -> comp -> ML (comp_typ & formula & guard_t)

//decorating terms with monadic operators
val maybe_lift: env -> term -> lident -> lident -> typ -> ML term
val maybe_monadic: env -> term -> lident -> typ -> ML term

val maybe_coerce_lc : env -> term -> lcomp -> typ -> ML (term & lcomp & guard_t)

(*
 * weaken_result_type env e lc t use_eq
 *   precondition: env |- e : lc
 * 
 * tries to weaken the result type of lc to t
 *
 * roughly checking that lc.result_typ <: t
 *
 * but if either (a) use_eq argument is true, or
 *               (b) env.use_eq is true, or
 *               (c) env.use_eq_strict is true, then checking that lc.result_typ = t
 *
 *)
val weaken_result_typ: env -> term -> lcomp -> typ -> bool -> ML (term & lcomp & guard_t)

val pure_or_ghost_pre_and_post: env -> comp -> ML (option typ & typ)

val norm_reify: env -> steps -> term -> ML term
val remove_reify: term -> ML term

//instantiation of implicits
val maybe_implicit_with_meta_or_attr: bqual -> list attribute -> ML bool

val instantiate_one_binder (env:env_t) (r:Range.t) (b:binder) : ML (term & typ & aqual & guard_t)
val maybe_instantiate : env -> term -> typ -> ML (term & typ & guard_t)

//
//checking that e:t is convertible to t'
//
//set the boolan flag to true if you want to check for type equality
//
val check_has_type : env -> term -> t:typ -> t':typ -> use_eq:bool -> ML guard_t
val check_has_type_maybe_coerce : env -> term -> lcomp -> typ -> bool -> ML (term & lcomp & guard_t)

val check_top_level: env -> guard_t -> lcomp -> ML (bool & comp)

val short_circuit: term -> args -> ML guard_formula
val short_circuit_head: term -> ML bool

val maybe_add_implicit_binders: env -> binders -> ML binders

val must_erase_for_extraction: env -> term -> ML bool

//layered effect utilities

val effect_extraction_mode : env -> lident -> ML eff_extraction_mode

(*
 * This function returns ed.repr<u> a ?u1 ... ?un (note that u must be the universe of a)
 *   where ?u1 ... ?un are unification variables, one for each index of the layered effect
 *
 * The unification variables are resolved in the input env
 *)
val fresh_effect_repr: env -> Range.t -> lident -> signature:tscheme -> repr:option tscheme -> u:universe -> a:term -> ML (term & guard_t)

(*
 * A wrapper over fresh_layered_effect_repr that looks up signature and repr from env
 *
 * If the effect does not have a repr (e.g. primitive effects), then we return a `unit -> M a ?u` term
 *)
val fresh_effect_repr_en: env -> Range.t -> lident -> universe -> term -> ML (term & guard_t)

(*
 * Return binders for the layered effect indices with signature
 * In the binder types, a is substituted with a_tm (u is universe of a)
 *)
val layered_effect_indices_as_binders:env -> Range.t -> eff_name:lident -> signature:tscheme -> u:universe -> a_tm:term -> ML binders

val get_field_projector_name : env -> datacon:lident -> index:int -> ML lident

(* update the env functions *)
val update_env_sub_eff : env -> sub_eff -> Range.t -> ML env
val update_env_polymonadic_bind :
  env -> lident -> lident -> lident -> tscheme -> indexed_effect_combinator_kind -> ML env

val try_lookup_record_type : env -> lident -> ML (option DsEnv.record_or_dc)
val head_fv_of_typ (_:env) (t:typ) : ML (option fv)
val find_record_or_dc_from_head_fv : env -> option fv -> unresolved_constructor -> Range.t -> ML (DsEnv.record_or_dc & lident & fv)
val field_name_matches : lident -> DsEnv.record_or_dc -> ident -> ML bool
val make_record_fields_in_order : env -> unresolved_constructor -> option (either typ typ) ->
                                DsEnv.record_or_dc ->
                                list (lident & 'a) ->
                                not_found:(ident -> ML (option 'a)) ->
                                Range.t ->
                                ML (list 'a)
