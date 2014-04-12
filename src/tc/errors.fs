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

open Microsoft.FStar.Absyn
open Microsoft.FStar.Util

let expected_arrow_kind k = 
  format1 "Expected a type-constructor or type-function; got a type of kind %s" (Print.kind_to_string k)

let expected_function_typ t = 
  format1 "Expected a function; got an expression of type %s" (Print.typ_to_string t)

let expected_poly_typ t = 
  format1 "Expected a polymorphic function; got an expression of type %s" (Print.typ_to_string t)

let nonlinear_pattern_variable x = 
  format1 "The pattern variable %s was used more than once" (Print.strBvd x)

let disjunctive_pattern_vars v1 v2 = 
  let vars v =
    v |> List.map (function 
      | Inl a -> Print.strBvd a 
      | Inr x ->  Print.strBvd x) |> String.concat ", " in
  format2 
    "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (%s) and another (%s)" 
    (vars v1) (vars v2)
  