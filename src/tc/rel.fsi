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
module Microsoft.FStar.Tc.RelOld

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Tc.Rel2
type guard_t = Rel2.guard_t
type guard_formula = Rel2.guard_formula

val new_kvar: Range.range -> binders -> knd * uvar_k
val new_tvar: Range.range -> binders -> knd -> typ * typ
val new_evar: Range.range -> binders -> typ -> exp * exp

val close_guard: binders -> guard_t -> guard_t
val apply_guard: guard_t -> exp -> guard_t
val trivial_guard: guard_t
val is_trivial: guard_t -> bool
val conj_guard: guard_t -> guard_t -> guard_t
val imp_guard: guard_t -> guard_t -> guard_t
val guard_of_guard_formula: guard_formula -> guard_t
val guard_f: guard_t -> guard_formula
val guard_to_string : env -> guard_t -> string
val try_discharge_guard: env -> guard_t -> (bool * list<string>)
val solve_deferred_constraints: env -> guard_t -> guard_t
val simplify_guard: env -> guard_t -> guard_t

val try_keq: env -> knd -> knd -> option<guard_t>
val keq : env -> option<typ> -> knd -> knd -> guard_t
val subkind: env -> knd -> knd -> guard_t
val try_teq: env -> typ -> typ -> option<guard_t>
val teq : env -> typ -> typ -> guard_t
val try_subtype: env -> typ -> typ -> option<guard_t>
val subtype: env -> typ -> typ -> guard_t
val subtype_fail: env -> typ -> typ -> 'a
val trivial_subtype: env -> option<exp> -> typ -> typ -> unit
val sub_comp: env -> comp -> comp -> option<guard_t>