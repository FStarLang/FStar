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

val info_at_pos (env:env) (file:string) (row col : int) : ML (option (either string lident & typ & Range.t))

val print_discrepancy (#a:Type) (#b:eqtype) (f : a -> ML b) (x : a) (y : a) : ML (b & b)

val errors_smt_detail
  (env : env)
  (errs : list Errors.error)
  (smt_detail : Errors.error_message)
: ML (list Errors.error)

val add_errors (env : env) (errs : list Errors.error) : ML unit

val log_issue (env : env) (r : Range.t) (ce : Errors.error_code & Errors.error_message) : ML unit

val log_issue_text (env : env) (r : Range.t) (e : Errors.error_code & string) : ML unit

val err_msg_type_strings (env : env) (t1 t2 : typ) : ML (string & string)

val err_msg_comp_strings (env : env) (c1 c2 : comp) : ML (string & string)

(* Error messages for labels in VCs *)
val exhaustiveness_check : Errors.error_message
val subtyping_failed : env -> typ -> typ -> unit -> ML Errors.error_message
val ill_kinded_type : Errors.error_message

val unexpected_signature_for_monad #a (env:env) (rng:Range.t) (m:lident) (k:term) : ML a
val expected_a_term_of_type_t_got_a_function #a (env:env) (rng:Range.t) (msg:string) (t:typ) (e:term) : ML a

val unexpected_implicit_argument :
  (Errors.error_code & string)

val expected_expression_of_type #a (env:env) (rng:Range.t) (t1 e t2 : term)  : ML a

val expected_pattern_of_type (env:env) (t1 e t2 : term) : ML (Errors.error_code & string)

val basic_type_error (env:env) (rng:Range.t) (eopt:option term) (t1 t2 : typ) : ML unit

val raise_basic_type_error #a (env:env) (rng:Range.t) (eopt:option term) (t1 t2 : typ) : ML a

val occurs_check : (Errors.error_code & string)

val constructor_fails_the_positivity_check (env:env) (d:term) (l:lid) : ML (Errors.error_code & string)

val inline_type_annotation_and_val_decl (l:lid) : ML (Errors.error_code & string)

val inferred_type_causes_variable_to_escape (env:env) (t:term) (x:bv) : ML (Errors.error_code & string)

val expected_function_typ #a (env:env) (rng:Range.t) (t:term) : ML a

val expected_poly_typ (env:env) (f:term) (t:typ) (targ:typ) :
  ML (Errors.error_code & string)

val disjunctive_pattern_vars (v1 v2 : list bv) : ML (Errors.error_code & string)

val computed_computation_type_does_not_match_annotation #a (env:env) (r:Range.t) (e:term) (c c':comp) : ML a

val computed_computation_type_does_not_match_annotation_eq #a (env:env) (r:Range.t) (e:term) (c c':comp) : ML a

val unexpected_non_trivial_precondition_on_term #a (env:env) (f:term) : ML a


val expected_pure_expression  #a (rng:Range.t) (e:term) (c:comp) (reason:option string) : ML a
val expected_ghost_expression #a (rng:Range.t) (e:term) (c:comp) (reason:option string) : ML a

val expected_effect_1_got_effect_2 (c1:lident) (c2:lident) : ML (Errors.error_code & string)
val failed_to_prove_specification_of (l:lbname) (lbls:list string) : ML (Errors.error_code & string)

val warn_top_level_effect (rng:Range.t) : ML unit
