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
module Bug190

noeq type form =
| FForall : (int -> Tot form) -> form

noeq type deduce : form -> Type =
  | DForallElim :
             f:(int->Tot form) ->
             deduce (FForall f) ->
             x:int ->
             deduce (f x)

type pred = int -> Tot form

val hoare_consequence : p:pred -> deduce (FForall (fun (h:int) -> p h)) -> h:int -> Tot unit
let hoare_consequence p vpp' h0 = ignore(DForallElim (fun (h : int) -> p h) vpp' h0)
