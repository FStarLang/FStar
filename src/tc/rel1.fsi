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
module Microsoft.FStar.Tc.Rel1

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Tc.Rel2
type guard_f = Rel2.guard_formula

val new_kvar: Range.range -> binders -> knd * uvar_k
val new_tvar: Range.range -> binders -> knd -> typ * typ
val new_evar: Range.range -> binders -> typ -> exp * exp

val guard_to_string : env -> guard_f -> string
val trivial : guard_f -> unit
val conj_guard: guard_f -> guard_f -> guard_f
val try_keq: env -> knd -> knd -> option<guard_f>
val keq : env -> option<typ> -> knd -> knd -> guard_f
val subkind: env -> knd -> knd -> guard_f
val try_teq: env -> typ -> typ -> option<guard_f>
val teq : env -> typ -> typ -> guard_f
val try_subtype: env -> typ -> typ -> option<guard_f>
val subtype: env -> typ -> typ -> guard_f
val subtype_fail: env -> typ -> typ -> 'a
val trivial_subtype: env -> option<exp> -> typ -> typ -> unit
val sub_comp: env -> comp -> comp -> option<guard_f>

val close_guard: binders -> guard_f -> guard_f
val apply_guard: guard_f -> exp -> guard_f
val try_discharge_guard: env -> guard_f -> (bool * list<string>)