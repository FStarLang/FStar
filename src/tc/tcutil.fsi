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

module FStar.Tc.Util

open FStar
open FStar.Tc
open FStar.Absyn
open FStar.Tc.Env
open FStar.Tc.Rel
open FStar.Absyn.Syntax

val report: env -> list<string> -> unit
val new_kvar : env -> knd
val new_tvar : env -> knd -> typ
val new_evar : env -> typ -> exp
val new_implicit_tvar : env -> knd -> (typ * (uvar_t * Range.range))
val new_implicit_evar : env -> typ -> (exp * (uvar_e * Range.range))
val as_uvar_t : typ -> uvar_t
val check_uvars: Range.range -> typ -> unit
val check_and_ascribe : env -> exp -> typ -> typ -> exp * Rel.guard_t
val pat_as_exps: bool -> env -> pat -> (list<Env.binding> * list<exp> * pat)
val decorate_pattern: env -> pat -> list<exp> -> pat
val decorated_pattern_as_exp: pat -> list<either_var> * exp
val decorated_pattern_as_typ: pat -> list<either_var> * typ
val decorated_pattern_as_either: pat -> list<either_var> * Util.either<typ,exp>

val maybe_instantiate_typ : env -> typ -> knd -> (typ * knd * implicits)
val maybe_instantiate : env -> exp -> typ -> (exp * typ * implicits)
val destruct_comp: comp_typ -> (typ * typ * typ)
val destruct_arrow_kind: env -> typ -> knd -> args -> (args * binders * knd)
val mk_basic_dtuple_type: env -> int -> typ
val extract_lb_annotation: env -> typ -> exp -> (exp * typ * bool)

(* most operations on computations are lazy *)
type lcomp_with_binder = option<Env.binding> * lcomp
val lcomp_of_comp: comp -> lcomp
val subst_lcomp: subst -> lcomp -> lcomp
val is_pure_effect: env -> lident -> bool
val is_pure_or_ghost_effect: env -> lident -> bool
val return_value: env -> typ -> exp -> comp
val bind: env -> option<exp> -> lcomp -> lcomp_with_binder -> lcomp
val bind_cases: env -> typ -> list<(typ * lcomp)> -> lcomp
val ite: env -> formula -> lcomp -> lcomp -> lcomp
val weaken_result_typ: env -> exp -> lcomp -> typ -> exp * lcomp * guard_t
val strengthen_precondition: option<(unit -> string)> -> env -> exp -> lcomp -> guard_t -> lcomp*guard_t
val weaken_guard: guard_formula -> guard_formula -> guard_formula
val weaken_precondition: env -> lcomp -> guard_formula -> lcomp
val maybe_assume_result_eq_pure_term: env -> exp -> lcomp -> lcomp
val close_comp: env -> list<binding> -> lcomp -> lcomp
val refresh_comp_label: env -> bool -> lcomp -> lcomp
val check_top_level: env -> guard_t -> lcomp -> bool*comp

(* Except these two, which require fully evaluated comp types *)
val check_comp: env -> exp -> comp -> comp -> exp * comp * guard_t
val generalize: bool -> env -> list<(lbname*exp*comp)> -> (list<(lbname*exp*comp)>)

val force_trivial: env -> guard_t -> unit
val discharge_guard: env -> guard_t -> unit
val label: string -> Range.range -> typ -> typ
val label_guard: string -> Range.range -> guard_formula -> guard_formula
val short_circuit_typ: Util.either<typ,exp> -> args -> guard_formula

val force_tk: syntax<'a,'b> -> 'b
val tks_of_args: args -> list<(Util.either<knd,typ> * aqual)>

val pure_or_ghost_pre_and_post: env -> comp -> (option<typ> * typ)