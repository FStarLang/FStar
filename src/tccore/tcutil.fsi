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
// (c) Microsoft Corporation. All rights reserved

module Microsoft.FStar.Tcutil

open Absyn

val handleable: exn -> bool
val handle_err: bool -> 'a -> exn -> 'a
val terr: Tcenv.env -> typ -> typ -> exp -> 'a 
val terr_p: Tcenv.env -> typ -> typ -> Range.range -> 'a 
val is_non_variable_value: Tcenv.env -> exp -> bool 
val kind_dominated: kind -> kind -> bool
val kind_lub: kind -> kind -> kind
val kind_abstractable: Range.range -> kind -> bool

type affines = list<bvvar>
val disjoint_affine_usages: affines -> bool
val subtract: list<bvar<'a,'b>> -> list<bvar<'a,'b>> -> list<bvar<'a,'b>>
val union: list<bvar<'a,'b>> -> list<bvar<'a,'b>> -> list<bvar<'a,'b>>

val lookup_field_in_record_typ: Range.range -> Tcenv.env -> lident -> typ -> typ

val is_implication: typ -> bool
val destruct_implication: typ -> option<typ*typ>
val is_pf_binop: lident -> typ -> bool
val destruct_pf_binop: lident -> typ -> option<typ*typ>
val maybe_eq_proof_typ: typ -> bool
val is_proof_typ_constr: typ -> bool
val is_proof_typ: typ -> bool
val is_tuple_typ: typ -> bool
val typing_const: Tcenv.env -> Sugar.sconst -> typ

val push_tparams: Tcenv.env -> list<tparam> -> Tcenv.env

val get_evidence: exp -> evidence
val get_evidencel: list<exp> -> evidence
val union_ev: evidence -> evidence -> evidence
val subtract_ev_exact: evidence -> evidence -> evidence
val subtract_ev: evidence -> list<Util.Disj<typ,exp>> -> evidence
(* val ascribe: exp -> typ -> evidence -> exp *)
(* val unascribe: exp -> exp *)
val collect_evidence: exp -> exp

val bot: typ -> exp
val is_closure_typ : Tcenv.env -> typ -> bool
val is_boxed : kind -> bool
val is_xvar_free : bvvdef -> typ -> bool
val is_tvar_free : btvdef -> typ -> bool
val reflexivity_var : Tcenv.env -> var<typ>
val eqT_of_typ : Tcenv.env -> typ -> typ
val unwrap_pf: typ -> typ

(* an equivalence class of unification variables, possibly unified to a typ *)
type subst = list<(list<uvar*kind> * option<typ>)> 
val check_unify: (uvar * kind) -> typ -> option<string>
val unify: uvar -> typ -> unit
val unify_subst_vars: subst -> unit

val mkTypApp : typ -> typ -> typ
val mkTypDep : typ -> exp -> typ

val reduce_typ_delta_beta: Tcenv.env -> typ -> typ
val rtdb: Tcenv.env -> typ -> typ
val generalize: Tcenv.env -> typ -> exp -> (typ * exp)
val generalize_with_constraints: Tcenv.env -> list<formula> -> typ -> exp -> (list<formula> * typ * exp) 
val extractSignature : Tcenv.env -> Absyn.modul -> list<sigelt> * list<sigelt>
