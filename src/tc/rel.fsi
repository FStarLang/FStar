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
module Microsoft.FStar.Tc.Rel

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Tc.Env

(* relations on types, kinds, etc. *)
type guard = 
  | Trivial
  | Guard of formula

val trivial : guard -> unit
val conj_guard: guard -> guard -> guard
val keq : env -> option<typ> -> knd -> knd -> guard
val teq : env -> typ -> typ -> guard
val try_subtype: env -> typ -> typ -> option<guard>
val subtype: env -> typ -> typ -> guard
val trivial_subtype: env -> option<exp> -> typ -> typ -> unit
val sub_comp: env -> comp -> comp -> option<guard>