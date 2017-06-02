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

module FStar.TypeChecker.Err
open FStar.All

open FStar
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Util
open FStar.TypeChecker.Normalize
open FStar.TypeChecker.Env
open FStar.Range
open FStar.Ident

module N = FStar.TypeChecker.Normalize
module BU = FStar.Util //basic util
open FStar.TypeChecker.Common

let info_at_pos env file row col =
    match TypeChecker.Common.info_at_pos file row col with
    | None -> None
    | Some info ->
      match info.identifier with
      | Inl bv -> Some (Inl (Print.nm_to_string bv), info.identifier_ty,
                       FStar.Syntax.Syntax.range_of_bv bv)
      | Inr fv -> Some (Inr (FStar.Syntax.Syntax.lid_of_fv fv), info.identifier_ty,
                       FStar.Syntax.Syntax.range_of_fv fv)

let add_errors env errs =
    let errs =
        errs |> List.map (fun (msg, r) ->
                        if r = dummyRange
                        then msg, Env.get_range env
                        else let r' = {r with def_range=r.use_range} in
                             if Range.file_of_range r' <> Range.file_of_range (Env.get_range env) //r points to another file
                             then (msg ^ ("(Also see: " ^ (Range.string_of_use_range r) ^")")), Env.get_range env
                             else msg, r) in
    FStar.Errors.add_errors errs

let err_msg_type_strings env t1 t2 :(string * string) =
  let s1 = N.term_to_string env t1 in
  let s2 = N.term_to_string env t2 in
  if s1 = s2 then
    Options.with_saved_options (fun _ ->
      ignore (Options.set_options Options.Set "--print_full_names --print_universes");
      N.term_to_string env t1, N.term_to_string env t2
    )
  else s1, s2

(* Error messages for labels in VCs *)
let exhaustiveness_check = "Patterns are incomplete"
let subtyping_failed : env -> typ -> typ -> unit -> string =
     fun env t1 t2 x ->
       let s1, s2 = err_msg_type_strings env t1 t2 in
       BU.format2 "Subtyping check failed; expected type %s; got type %s" s2 s1
let ill_kinded_type = "Ill-kinded type"
let totality_check  = "This term may not terminate"

let unexpected_signature_for_monad env m k =
  format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
    m.str (N.term_to_string env k)

let expected_a_term_of_type_t_got_a_function env msg t e =
  format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
    (N.term_to_string env t) (Print.term_to_string e) msg

let unexpected_implicit_argument =
  "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type env t1 e t2 =
  let s1, s2 = err_msg_type_strings env t1 t2 in
  format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
    s1 (Print.term_to_string e) s2

let expected_function_with_parameter_of_type env t1 t2 =
  let s1, s2 = err_msg_type_strings env t1 t2 in
  format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
    s1 s2

let expected_pattern_of_type env t1 e t2 =
  let s1, s2 = err_msg_type_strings env t1 t2 in
  format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
    s1 (Print.term_to_string e) s2

let basic_type_error env eopt t1 t2 =
  let s1, s2 = err_msg_type_strings env t1 t2 in
  match eopt with
    | None -> format2 "Expected type \"%s\"; got type \"%s\"" s1 s2
    | Some e -> format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1 (Print.term_to_string e) s2

let occurs_check =
  "Possibly infinite typ (occurs check failed)"

let unification_well_formedness =
  "Term or type of an unexpected sort"

let incompatible_kinds env k1 k2 =
  format2 "Kinds \"%s\" and \"%s\" are incompatible"
    (N.term_to_string env k1) (N.term_to_string env k2)

let constructor_builds_the_wrong_type env d t t' =
  format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
    (Print.term_to_string d) (N.term_to_string env t) (N.term_to_string env t')

let constructor_fails_the_positivity_check env d l =
  format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    (Print.term_to_string d) (Print.lid_to_string l)

let inline_type_annotation_and_val_decl l =
  format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" (Print.lid_to_string l)

(* CH: unsure if the env is good enough for normalizing t here *)
let inferred_type_causes_variable_to_escape env t x =
  format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
    (N.term_to_string env t) (Print.bv_to_string x)

let expected_function_typ env t =
  format1 "Expected a function; got an expression of type \"%s\""
    (N.term_to_string env t)

let expected_poly_typ env f t targ =
  format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
    (Print.term_to_string f) (N.term_to_string env t) (N.term_to_string env targ)

let nonlinear_pattern_variable x =
  let m = Print.bv_to_string x in
  format1 "The pattern variable \"%s\" was used more than once" m

let disjunctive_pattern_vars v1 v2 =
  let vars v =
    v |> List.map Print.bv_to_string |> String.concat ", " in
  format2
    "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
    (vars v1) (vars v2)

let name_and_result c = match c.n with
  | Total (t, _) -> "Tot", t
  | GTotal (t, _) -> "GTot", t
  | Comp ct -> Print.lid_to_string ct.effect_name, ct.result_typ

let computed_computation_type_does_not_match_annotation env e c c' =
  let f1, r1 = name_and_result c in
  let f2, r2 = name_and_result c' in
  let s1, s2 = err_msg_type_strings env r1 r2 in
  format4
    "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
      s1 f1 s2 f2

let unexpected_non_trivial_precondition_on_term env f =
 format1 "Term has an unexpected non-trivial pre-condition: %s" (N.term_to_string env f)

let expected_pure_expression e c =
  format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" (Print.term_to_string e) (fst <| name_and_result c)

let expected_ghost_expression e c =
  format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" (Print.term_to_string e) (fst <| name_and_result c)

let expected_effect_1_got_effect_2 (c1:lident) (c2:lident) =
  format2 "Expected a computation with effect %s; but it has effect %s" (Print.lid_to_string c1) (Print.lid_to_string c2)

let failed_to_prove_specification_of l lbls =
  format2 "Failed to prove specification of %s; assertions at [%s] may fail" (Print.lbname_to_string l) (lbls |> String.concat ", ")

let failed_to_prove_specification lbls =
  match lbls with
    | [] -> "An unknown assertion in the term at this location was not provable"
    | _ -> format1 "The following problems were found:\n\t%s" (lbls |> String.concat "\n\t")

let top_level_effect = "Top-level let-bindings must be total; this term may have effects"

let cardinality_constraint_violated l a =
    format2 "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed" (Print.lid_to_string l) (Print.bv_to_string a.v)
