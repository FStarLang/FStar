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

module Microsoft.FStar.Tc.Errors

open Microsoft.FStar
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Util

(* Error messages for labels in VCs *)
let exhaustiveness_check = "Patterns are incomplete"
let subtyping_check t1 t2 = Util.format2 "Subtyping check failed; expected type %s; got type %s" (Print.typ_to_string t2) (Print.typ_to_string t1)
let ill_kinded_type = "Ill-kinded type"
let totality_check  = "This term may not terminate"

let diag r msg = 
  Util.print_string (format2 "Diagnostic %s: %s\n" (Range.string_of_range r) msg)

let warn r msg = 
  Util.print_string (format2 "Diagnostic %s: %s\n" (Range.string_of_range r) msg)

let num_errs = Util.mk_ref 0
let report r msg = 
  incr num_errs;
  Util.print_string (format2 "Error %s: %s\n" (Range.string_of_range r) msg)
let get_err_count () = !num_errs

let ill_kinded_effect e k = 
  format2 "Ill-kinded effect (%s) has kind %s" e.str (Print.kind_to_string k)

let unexpected_signature_for_monad m k = 
  format2 "Unexpected signature for monad \"%s\". Expected a kind of the form ('a:Type => WP 'a => WP 'a => Type);\ngot %s" m.str (Print.kind_to_string k)

let name_not_found (l:Syntax.lident) = 
  format1 "Name \"%s\" not found" l.str

let expected_a_term_of_type_t_got_a_function t e = 
  format2 "Expected a term of type \"%s\";\ngot a function \"%s\"" (Print.typ_to_string t) (Print.exp_to_string e)

let variable_not_found v = 
  format1 "Variable \"%s\" not found" (Print.strBvd v) 

let unexpected_implicit_argument = 
  "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type t1 e t2 = 
  format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" (Print.typ_to_string t1) (Print.exp_to_string e) (Print.typ_to_string t2)

let expected_function_with_parameter_of_type t1 t2 = 
  format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" (Print.typ_to_string t1) (Print.typ_to_string t2)

let expected_pattern_of_type t1 e t2 = 
  format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" (Print.typ_to_string t1) (Print.exp_to_string e) (Print.typ_to_string t2)

let basic_type_error eopt t1 t2 = 
  match eopt with 
    | None -> format2 "Expected type \"%s\";\ngot type \"%s\"" (Print.typ_to_string t1) (Print.typ_to_string t2)
    | Some e -> format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" (Print.typ_to_string t1) (Print.exp_to_string e) (Print.typ_to_string t2)
  
let occurs_check = 
  "Possibly infinite typ (occurs check failed)"

let unification_well_formedness = 
  "Term or type of an unexpected sort"

let incompatible_kinds k1 k2 = 
  format2 "Kinds \"%s\" and \"%s\" are incompatible" (Print.kind_to_string k1) (Print.kind_to_string k2)

let constructor_builds_the_wrong_type d t t' = 
  format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" (Print.exp_to_string d) (Print.typ_to_string t) (Print.typ_to_string t')

let inline_type_annotation_and_val_decl l = 
  format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" (Print.sli l)

let inferred_type_causes_variable_to_escape t x = 
  format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" (Print.typ_to_string t) (Print.strBvd x)
  
let expected_typ_of_kind k1 t k2 =
  format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\""  (Print.kind_to_string k1) (Print.typ_to_string t) (Print.kind_to_string k2)

let expected_tcon_kind t k = 
  format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" (Print.typ_to_string t) (Print.kind_to_string k)

let expected_dcon_kind t k = 
  format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" (Print.typ_to_string t) (Print.kind_to_string k)

let expected_function_typ t = 
  format1 "Expected a function;\ngot an expression of type \"%s\"" (Print.typ_to_string t)

let expected_poly_typ f t targ = 
  format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" (Print.exp_to_string f) (Print.typ_to_string t) (Print.typ_to_string targ)

let nonlinear_pattern_variable x = 
  let m = match x with 
    | Inl x -> Print.strBvd x.v
    | Inr a -> Print.strBvd a.v in
  format1 "The pattern variable \"%s\" was used more than once" m

let disjunctive_pattern_vars v1 v2 = 
  let vars v =
    v |> List.map (function 
      | Inl a -> Print.strBvd a.v 
      | Inr x ->  Print.strBvd x.v) |> String.concat ", " in
  format2 
    "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" 
    (vars v1) (vars v2)
 
let name_and_result c = match c.n with
  | Total t -> "Tot", t
  | Comp ct -> Print.sli ct.effect_name, ct.result_typ

let computed_computation_type_does_not_match_annotation e c c' = 
  let f1, r1 = name_and_result c in
  let f2, r2 = name_and_result c' in
  format4    
    "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" 
      (Print.typ_to_string r1) f1 (Print.typ_to_string r2) f2

let unexpected_non_trivial_precondition_on_term f = 
  Util.format1 "Term has an unexpected non-trivial pre-condition: %s" (Print.formula_to_string f)

let type_has_a_non_trivial_precondition t = 
  format1 "Type \"%s\" has an unexpected non-trivial pre-condition" (Print.typ_to_string t)

let kind_has_a_non_trivial_precondition k = 
  format1 "Kind \"%s\" has an unexpected non-trivial pre-condition" (Print.kind_to_string k)

let expected_pure_expression e c =
  format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" (Print.exp_to_string e) (fst <| name_and_result c)

let expected_effect_1_got_effect_2 (c1:lident) (c2:lident) =
  format2 "Expected a computation with effect %s; but it has effect %s\n" (Print.sli c1) (Print.sli c2)

let failed_to_prove_specification_of l lbls = 
  format2 "Failed to prove specification of %s; assertions at [%s] may fail" (Print.lbname_to_string l) (lbls |> String.concat ", ")

let failed_to_prove_specification lbls = 
  match lbls with 
    | [] -> "An unknown assertion in the term at this location was not provable"
    | _ -> format1 "The following problems were found:\n\t%s" (lbls |> String.concat "\n\t")