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
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Tc.Rel

val t_bool : typ
val t_unit : typ
val typing_const : env -> sconst -> typ
val push_tparams : env -> list<tparam> -> env
val new_kvar : env -> knd          
val new_tvar : env -> knd -> typ
val new_evar : env -> typ -> exp
val check_uvars: Range.range -> typ -> unit
val check_and_ascribe : env -> exp -> typ -> typ -> exp * Rel.guard
val pat_as_exps: env -> pat -> list<exp>
val generalize: env -> list<(lbname*exp*comp)> -> (list<(lbname*exp*comp)>)
val maybe_instantiate : env -> exp -> typ -> (exp * comp)
val destruct_comp: comp_typ -> (typ * typ * typ)
val destruct_function_typ : env -> typ -> option<bvvdef> -> option<exp> -> bool -> bool -> (typ * option<exp>)
val destruct_poly_typ: env -> typ -> exp -> typ -> (typ*exp) 
val destruct_tcon_kind: env -> knd -> typ -> bool -> (knd*typ)
val destruct_dcon_kind: env -> knd -> typ -> bool -> (knd*typ)
val mk_basic_dtuple_type: env -> int -> typ
val extract_lb_annotation: bool -> env -> typ -> exp -> typ

type comp_with_binder = option<Env.binding> * comp
val is_pure: env -> comp -> bool
val return_value: env -> typ -> exp -> comp
val bind: env -> comp -> comp_with_binder -> comp
val bind_cases: env -> typ -> list<(option<typ> * comp)> -> comp
val weaken_result_typ: env -> exp -> comp -> typ -> exp * comp
val strengthen_precondition: env -> comp -> guard -> comp
val weaken_precondition: env -> comp -> guard -> comp
val maybe_assume_result_eq_pure_term: env -> exp -> comp -> comp
val lift_pure: env -> typ -> formula -> comp (* with t as a result type *)
val close_guard: list<Tc.Env.binding> -> guard -> guard
val close_comp: env -> list<binding> -> comp -> comp
val check_comp: env -> exp -> comp -> comp -> exp * comp * guard
val refine_data_type: env -> lident -> list<Util.either<(btvdef * knd), (option<bvvdef> * typ * bool)>> -> typ -> typ
