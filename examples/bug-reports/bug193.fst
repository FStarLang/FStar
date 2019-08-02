(*
   Copyright 2008-2018 Microsoft Research

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
module Bug193

type form =
| FTrue   : form
| FImpl   : form -> form -> form

type deduce : form -> Type =
  | DImplIntro :
             #f1:form ->
             #f2:form ->
             (deduce f1 -> Tot (deduce f2)) -> (* <-- meta level implication *)
             deduce (FImpl f1 f2)

type pred = heap -> Tot form

val wlp_sound : q:pred -> Tot unit
let rec wlp_sound q =
  ignore(fun h -> (DImplIntro (*#FTrue #FTrue*) (fun pq -> pq)))
