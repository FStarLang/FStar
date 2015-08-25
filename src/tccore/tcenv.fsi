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
// (c) Microsoft Corporation. All rights reserved

module FStar.Tcenv

open Absyn 

type binding =
  | Binding_var of ident * typ
  | Binding_typ of ident * kind
  | Binding_match of exp * exp   (* term equalities induced by pattern matching value-indexed types *)
  | Binding_tmatch of btvar * typ  (* type equalities induced by GADT-style pattern matching *)

(* type env *)
type sigtable = HashMultiMap<string, sigelt>
type phase = | TC | DEREFINE 
type env = {
  range:Range.range;
  phase:phase;
  curmodule: lident;             (* Name of this module---the "principal" subscript *)
  gamma:list<binding>;           (* Main typing environment *)
  externs: signature;            (* Extern declarations accumulated from other modules *)
  e_signature: signature;        (* Type and data constructors for this module *)
  curunit: lident;               (* the name of the current top-level function unit *)
  in_typ_decl: bool;             (* are we currently checking a type declaration*)
  modules:list<lident * modul>;  (* already fully type checked modules *)
  expected_typ:option<typ>;
  recall_expected_typ:option<typ>;
  expected_kind:option<kind>;
  expect_tyapps:bool;
  current_value:option<exp>;
  solver:option<solver>;
  kind_level:bool;
  sigtab:sigtable;
  sigtab_typ:sigtable;
  extern_typ:bool;
  expand_externs:bool;
  object_invariants:bool;
  skip_kinding:bool;
  uvars:list<uvar>;
  annot:option<string>;
}
and solver = {solver_toggle_caching: unit -> unit; 
              solver_query: env -> typ -> bool; 
              solver_query_equiv: env -> exp -> exp -> bool;
              solver_discharge_proof: env -> typ -> option<exp>}

val set_range : env -> Range.range -> env
val get_range : env -> Range.range 
val in_tc_phase: env -> bool
val set_tc_phase: env -> env
val in_derefinement_phase: env -> bool
val set_derefinement_phase: env -> env

val initial_env: lident -> solver -> env
val mk_env: unit -> env
val empty_env: env
val modules : env -> list<lident*modul>
val signature : env -> signature
val set_solver: env -> solver -> env
val use_solver : env -> bool
val get_solver: env -> option<solver>
val clear_solver: env -> env

val set_kind_level : env -> env
val is_kind_level : env -> bool

exception Not_found_binding of env * Util.Disj<typ',exp'>

val current_module : env -> lident
val set_current_module : env -> lident -> env
val current_unit : env -> lident
val set_current_unit : env -> lident -> env
val in_typ_decl : env -> bool
val set_in_typ_decl : env -> env
val clear_in_typ_decl : env -> env

val lookup_val_decl: env -> lident -> typ
val lookup_bvar_ident : env -> ident -> option<typ>
val lookup_bvar : env -> bvvar -> typ
val lookup_lid : env -> lident -> typ
val lookup_fvar : env -> var<typ> -> option<typ>
val lookup_fvar_with_params : env -> var<typ> -> option<(typ * list<tparam>)>
val lookup_operator: env -> ident -> option<typ>

val lookup_typ_abbrev: (env -> var<kind> -> option<typ>)
val lookup_btvar_ident : env -> ident -> option<kind>
val lookup_btvar : env -> btvar -> kind
val lookup_typ_const : env -> var<kind> -> kind
val lookup_typ_lid : env -> lident -> kind
val lookup_field_name : env -> lident -> (list<tparam> * typ)
val field_name_exists : env -> lident -> bool
val lookup_record_typ : env -> lident -> (lident * typ * list<tparam> * typ) (* first type is the abbreviation as type name *)
val lookup_record_typ_by_name : env -> lident -> (lident * typ * list<tparam> * typ) 
val get_record_fields: Range.range -> env -> typ -> list<fieldname*typ>
val is_datacon: env -> var<typ> -> bool
val is_logic_function: env -> var<typ> -> bool
val is_logic_data: env -> lident -> bool
val is_logic_array: env -> lident -> bool
val is_record: env -> lident -> bool
val is_prop: env -> typ -> bool
val lookup_datatype : env -> lident -> option<signature>

val push_sigelt : env -> sigelt -> env
val push_local_binding : env -> binding -> env
val push_local_binding_fast : env -> binding -> env
val push_module : env -> modul -> env
val set_expected_typ : env -> typ -> env 
val expected_typ : env -> option<typ> 
val clear_expected_typ : env -> (env * option<typ>)
val recall_expected_typ : env -> option<typ>
val set_expected_kind : env -> kind -> env 
val expected_kind : env -> option<kind> 
val clear_expected_kind : env -> (env * option<kind>)
val uvars_in_env: env -> list<uvar>

val clear_current_state : env -> env

val stfold : env -> (binding -> Util.state<'s,unit>) -> Util.state<'s,unit>
val stfoldr : env -> (env -> binding -> Util.state<'s,unit>) -> Util.state<'s,unit>
val fold_env : env -> ('a -> binding -> 'a) -> 'a -> 'a
val find: env -> (binding -> bool) -> option<binding>

val set_expect_tyapps : env -> env
val clear_expect_tyapps : env -> env
val expect_tyapps : env -> bool
val dump: env -> unit

val freevars_not_in_env : env -> typ -> (list<btvar> * list<bvvar>)

val set_current_value : env -> exp -> env
val current_value : env -> option<exp>
val clear_current_value : env -> env

val expand_typ: env -> typ -> typ
val expand_typ_until_pred: env -> typ -> (typ -> bool) -> option<typ>
val expand_typ_until: env -> typ -> lident -> option<typ>
val expand_typ_rec: env -> typ -> typ (* expensive! use with care *)
val expand_exp_rec: env -> exp -> exp (* expensive! use with care *)


val tycon_kind_from_tparams : list<tparam> -> kind -> kind
val get_sigtab_keys: env -> list<string>

val dcon_type_from_tparams: list<tparam> -> typ -> typ

val set_extern_typ : env -> env
val extern_typ : env -> bool
val clear_extern_typ : env -> env
val clear_expand_externs : env -> env
val set_expand_externs : env -> env

val patternEnv : env -> typ -> env 
val bindings: env -> string
