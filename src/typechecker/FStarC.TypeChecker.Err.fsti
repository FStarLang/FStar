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
module FStarC.TypeChecker.Err

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.Ident

val info_at_pos (env:env) (file:string) (row col : int) : option (either string lident & typ & Range.t)

(* Will attempt to enable certain printing flags to make x and y
 * visibly different. It will try to enable the least possible
 * subset of implicits, universes, effect_args and full_names.
 * It will also prioritize them in that order, prefering to show
 * a discrepancy of implicits before one of universes, etc.
 *)
val print_discrepancy (#a:Type) (#b:eqtype) (f : a -> b) (x : a) (y : a) : b & b

val errors_smt_detail
  (env : env)
  (errs : list Errors.error)
  (smt_detail : Errors.error_message)
: list Errors.error

val add_errors (env : env) (errs : list Errors.error) : unit

val log_issue (env : env) (r : Range.t) (ce : Errors.error_code & Errors.error_message) : unit

val log_issue_text (env : env) (r : Range.t) (e : Errors.error_code & string) : unit

val err_msg_type_strings (env : env) (t1 t2 : typ) : string & string

val err_msg_comp_strings (env : env) (c1 c2 : comp) : string & string

(* Error messages for labels in VCs *)
val exhaustiveness_check : Errors.error_message
val subtyping_failed : env -> typ -> typ -> unit -> Errors.error_message
val ill_kinded_type : Errors.error_message

val unexpected_signature_for_monad #a (env:env) (rng:Range.t) (m:lident) (k:term) : a
val expected_a_term_of_type_t_got_a_function #a (env:env) (rng:Range.t) (msg:string) (t:typ) (e:term) : a

val unexpected_implicit_argument :
  (Errors.error_code & string)

val expected_expression_of_type #a (env:env) (rng:Range.t) (t1 e t2 : term)  : a

val expected_pattern_of_type (env:env) (t1 e t2 : term) : (Errors.error_code & string)

val basic_type_error (env:env) (rng:Range.t) (eopt:option term) (t1 t2 : typ) : unit

(* It does not make sense to use the same code for a catcheable and uncatcheable
error, but that's what this was doing. *)
val raise_basic_type_error #a (env:env) (rng:Range.t) (eopt:option term) (t1 t2 : typ) : a

val occurs_check : (Errors.error_code & string)

val constructor_fails_the_positivity_check (env:env) (d:term) (l:lid) : (Errors.error_code & string)

val inline_type_annotation_and_val_decl (l:lid) : (Errors.error_code & string)

(* CH: unsure if the env is good enough for normalizing t here *)
val inferred_type_causes_variable_to_escape (env:env) (t:term) (x:bv) : (Errors.error_code & string)

val expected_function_typ #a (env:env) (rng:Range.t) (t:term) : a

val expected_poly_typ (env:env) (f:term) (t:typ) (targ:typ) :
  Errors.error_code & string

val disjunctive_pattern_vars (v1 v2 : list bv) : (Errors.error_code & string)

val computed_computation_type_does_not_match_annotation #a (env:env) (r:Range.t) (e:term) (c c':comp) : a

val computed_computation_type_does_not_match_annotation_eq #a (env:env) (r:Range.t) (e:term) (c c':comp) : a

val unexpected_non_trivial_precondition_on_term #a (env:env) (f:term) : a


val expected_pure_expression  #a (rng:Range.t) (e:term) (c:comp) (reason:option string) : a
val expected_ghost_expression #a (rng:Range.t) (e:term) (c:comp) (reason:option string) : a

val expected_effect_1_got_effect_2 (c1:lident) (c2:lident) : (Errors.error_code & string)
val failed_to_prove_specification_of (l:lbname) (lbls:list string) : (Errors.error_code & string)

val warn_top_level_effect (rng:Range.t) : unit
