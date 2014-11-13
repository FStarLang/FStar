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

module Microsoft.FStar.Tc.Util

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Tc.Rel
open Microsoft.FStar.Absyn.Syntax

val t_bool : typ
val t_unit : typ
val typing_const : env -> sconst -> typ
val new_kvar : env -> knd          
val new_tvar : env -> knd -> typ
val new_evar : env -> typ -> exp
val check_uvars: Range.range -> typ -> unit
val check_and_ascribe : env -> exp -> typ -> typ -> exp * Rel.guard_t
val pat_as_exps: env -> pat -> list<Env.binding> * list<Env.binding> * list<exp>
val decorate_pattern: pat -> list<exp> -> pat
val decorated_pattern_as_exp: pat -> list<either_var> * exp
val decorated_pattern_as_typ: pat -> list<either_var> * typ
val decorated_pattern_as_either: pat -> list<either_var> * Util.either<typ,exp>

val generalize: env -> list<(lbname*exp*comp)> -> (list<(lbname*exp*comp)>)
val maybe_instantiate : env -> exp -> typ -> (exp * typ)
val destruct_comp: comp_typ -> (typ * typ * typ)
//val new_function_typ: env -> option<bvvdef> -> option<lident> -> typ
//val new_poly_typ: env -> btvdef -> typ
//val uvar_as_function_typ: env -> option<typ> -> option<bvvdef> -> option<lident> -> typ

//val destruct_function_typ : env -> typ -> option<bvvdef> -> option<exp> -> bool -> option<lident> -> (typ * option<exp>)
//val destruct_poly_typ: env -> typ -> exp -> typ -> (typ*exp) 
val destruct_arrow_kind: env -> typ -> knd -> args -> (args * binders * knd)
val mk_basic_dtuple_type: env -> int -> typ
val extract_lb_annotation: bool -> env -> typ -> exp -> (exp * typ)

type comp_with_binder = option<Env.binding> * comp
val is_pure: env -> comp -> bool
val return_value: env -> typ -> exp -> comp
val bind: env -> option<exp> -> comp -> comp_with_binder -> comp
val bind_cases: env -> typ -> list<(typ * comp)> -> comp
val weaken_result_typ: env -> exp -> comp -> typ -> exp * comp
val strengthen_precondition: option<(unit -> string)> -> env -> comp -> guard_t -> comp
val weaken_precondition: env -> comp -> guard_t -> comp
val maybe_assume_result_eq_pure_term: env -> exp -> comp -> comp
val lift_pure: env -> typ -> formula -> comp (* with t as a result type *)
val close_guard: binders -> guard_t -> guard_t
val close_comp: env -> list<binding> -> comp -> comp
val check_comp: env -> exp -> comp -> comp -> exp * comp * guard_t

val discharge_guard: env -> guard_t -> unit
val label: string -> Range.range -> typ -> typ
val label_guard: string -> Range.range -> guard_t -> guard_t
val refresh_comp_label: env -> bool -> comp -> comp
val check_total: env -> comp -> bool * list<string>

