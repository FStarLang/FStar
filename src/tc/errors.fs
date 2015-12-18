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

module FStar.Tc.Errors

open FStar
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Util

open FStar.Tc
open FStar.Tc.Env
open FStar.Tc.Normalize

(* Error messages for labels in VCs *)
let exhaustiveness_check = "Patterns are incomplete"
let subtyping_failed : env -> typ -> typ -> unit -> string =
     fun env t1 t2 x -> Util.format2 "Subtyping check failed; expected type %s; got type %s"
        (Normalize.typ_norm_to_string env t2) (Normalize.typ_norm_to_string env t1)
let ill_kinded_type = "Ill-kinded type"
let totality_check  = "This term may not terminate"

let diag r msg =
  Util.print_string (format2 "%s (Diagnostic): %s\n" (Range.string_of_range r) msg)

let warn r msg =
  Util.print_string (format2 "%s (Warning): %s\n" (Range.string_of_range r) msg)

let num_errs = Util.mk_ref 0
let verification_errs : ref<list<(Range.range * string)>> = Util.mk_ref []
let add_errors env errs =
    let errs = errs |> List.map (fun (msg, r) -> let r = if r=dummyRange then Env.get_range env else r in (r, msg)) in
    let n_errs = List.length errs in
    atomically (fun () ->
        verification_errs := errs@ (!verification_errs);
        num_errs := !num_errs + n_errs)
let report_all () =
    let all_errs = atomically (fun () -> let x = !verification_errs in verification_errs := []; x) in
    let all_errs = List.sortWith (fun (r1, _) (r2, _) -> Range.compare r1 r2) all_errs in
    all_errs |> List.iter (fun (r, msg) -> Util.print2 "%s: %s\n" (Range.string_of_range r) msg);
    List.length all_errs


let report r msg =
  incr num_errs;
  Util.print_string (format2 "%s: %s\n" (Range.string_of_range r) msg)
let get_err_count () = !num_errs

let unexpected_signature_for_monad env m k =
  format2 "Unexpected signature for monad \"%s\". Expected a kind of the form ('a:Type => WP 'a => WP 'a => Type);\ngot %s"
    m.str (Normalize.kind_norm_to_string env k)

let expected_a_term_of_type_t_got_a_function env msg t e =
  format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)"
    (Normalize.typ_norm_to_string env t) (Print.exp_to_string e) msg

let unexpected_implicit_argument =
  "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type env t1 e t2 =
  format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\""
    (Normalize.typ_norm_to_string env t1) (Print.exp_to_string e) (Normalize.typ_norm_to_string env t2)

let expected_function_with_parameter_of_type env t1 t2 =
  format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
    (Normalize.typ_norm_to_string env t1) (Normalize.typ_norm_to_string env t2)

let expected_pattern_of_type env t1 e t2 =
  format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\""
    (Normalize.typ_norm_to_string env t1) (Print.exp_to_string e) (Normalize.typ_norm_to_string env t2)

let basic_type_error env eopt t1 t2 =
  match eopt with
    | None -> format2 "Expected type \"%s\";\ngot type \"%s\""
                (Normalize.typ_norm_to_string env t1) (Normalize.typ_norm_to_string env t2)
    | Some e -> format3 "Expected type \"%s\"; but \"%s\" has type \"%s\""
                (Normalize.typ_norm_to_string env t1) (Print.exp_to_string e) (Normalize.typ_norm_to_string env t2)

let occurs_check =
  "Possibly infinite typ (occurs check failed)"

let unification_well_formedness =
  "Term or type of an unexpected sort"

let incompatible_kinds env k1 k2 =
  format2 "Kinds \"%s\" and \"%s\" are incompatible"
    (Normalize.kind_norm_to_string env k1) (Normalize.kind_norm_to_string env k2)

let constructor_builds_the_wrong_type env d t t' =
  format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
    (Print.exp_to_string d) (Normalize.typ_norm_to_string env t) (Normalize.typ_norm_to_string env t')

let constructor_fails_the_positivity_check env d l =
  format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    (Print.exp_to_string d) (Print.sli l)

let inline_type_annotation_and_val_decl l =
  format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" (Print.sli l)

(* CH: unsure if the env is good enough for normalizing t here *)
let inferred_type_causes_variable_to_escape env t x =
  format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
    (Normalize.typ_norm_to_string env t) (Print.strBvd x)

let expected_typ_of_kind env k1 t k2 =
  format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\""
    (Normalize.kind_norm_to_string env k1) (Normalize.typ_norm_to_string env t) (Normalize.kind_norm_to_string env k2)

let expected_tcon_kind env t k =
  format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\""
    (Normalize.typ_norm_to_string env t) (Normalize.kind_norm_to_string env k)

let expected_dcon_kind env t k =
  format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\""
    (Normalize.typ_norm_to_string env t) (Normalize.kind_norm_to_string env k)

let expected_function_typ env t =
  format1 "Expected a function;\ngot an expression of type \"%s\""
    (Normalize.typ_norm_to_string env t)

let expected_poly_typ env f t targ =
  format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\""
    (Print.exp_to_string f) (Normalize.typ_norm_to_string env t) (Normalize.typ_norm_to_string env targ)

let nonlinear_pattern_variable x =
  let m = match x with
    | Inl x -> Print.strBvd x
    | Inr a -> Print.strBvd a in
  format1 "The pattern variable \"%s\" was used more than once" m

let disjunctive_pattern_vars v1 v2 =
  let vars v =
    v |> List.map (function
      | Inl a -> Print.strBvd a
      | Inr x -> Print.strBvd x) |> String.concat ", " in
  format2
    "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
    (vars v1) (vars v2)

let name_and_result c = match c.n with
  | Total t -> "Tot", t
  | Comp ct -> Print.sli ct.effect_name, ct.result_typ

let computed_computation_type_does_not_match_annotation env e c c' =
  let f1, r1 = name_and_result c in
  let f2, r2 = name_and_result c' in
  format4
    "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
      (Normalize.typ_norm_to_string env r1) f1 (Normalize.typ_norm_to_string env r2) f2

let unexpected_non_trivial_precondition_on_term env f =
 format1 "Term has an unexpected non-trivial pre-condition: %s" (Normalize.formula_norm_to_string env f)

let expected_pure_expression e c =
  format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" (Print.exp_to_string e) (fst <| name_and_result c)

let expected_ghost_expression e c =
  format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" (Print.exp_to_string e) (fst <| name_and_result c)

let expected_effect_1_got_effect_2 (c1:lident) (c2:lident) =
  format2 "Expected a computation with effect %s; but it has effect %s\n" (Print.sli c1) (Print.sli c2)

let failed_to_prove_specification_of l lbls =
  format2 "Failed to prove specification of %s; assertions at [%s] may fail" (Print.lbname_to_string l) (lbls |> String.concat ", ")

let failed_to_prove_specification lbls =
  match lbls with
    | [] -> "An unknown assertion in the term at this location was not provable"
    | _ -> format1 "The following problems were found:\n\t%s" (lbls |> String.concat "\n\t")

let top_level_effect = "Top-level let-bindings must be total; this term may have effects"

let cardinality_constraint_violated l a = 
    Util.format2 "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed" (Print.sli l) (Print.strBvd a.v)