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
module FStar.TypeRelations

open Absyn
open Tcutil

type equatables<'a,'sort>=list<bvar<'a,'sort>>
val debug : bool ref
val instantiable: Tcenv.env -> equatables<exp,typ> -> equatables<typ,kind> -> typ -> typ -> option<subst * list<Tcenv.binding>>
val convertible_ev: Tcenv.env -> typ -> typ -> option<subst * evidence>
val kind_convertible_ev : Tcenv.env -> kind -> kind -> option<subst * evidence>
val force_kind_convertible_ev : Tcenv.env -> kind -> kind -> option<evidence>

val equiv: Tcenv.env -> typ -> typ -> option<subst>
val equivalent_with_evidence: Tcenv.env -> typ -> typ -> option<evidence>
val equivalent_with_equations: Tcenv.env -> equatables<exp,typ> -> typ -> typ -> option<list<Tcenv.binding>>
val equivalent_kinds_with_evidence: Tcenv.env -> kind -> kind -> option<evidence>
val alpha_equiv: Tcenv.env -> typ -> typ -> bool

val new_uvar: Tcenv.env -> kind -> Range.range -> typ
val instantiate_kind: Tcenv.env -> typ -> kind -> (typ * kind) 

(* (instantiate_typ G (forall a1..an. t)) --> (t[u1..un/a1..an], ([(a1,u1), ..., (an,un)])) *)
val instantiate_typ_gen_constraints : Tcenv.env -> typ -> (list<formula> * typ * list<(btvdef*typ)>)
val instantiate_typ : Tcenv.env -> typ -> (typ * list<(btvdef*typ)>)
val instantiate_typ_with_actuals : Tcenv.env -> typ -> list<typ> -> check_kind:(typ -> kind -> typ) -> (typ * list<(btvdef*typ)>)

val try_instantiate_final_typ: Tcenv.env -> tparam list -> typ -> typ -> typ * (bvvdef * exp) list

val formula_entailment : Tcenv.env -> list<formula> -> bool
val formula_implication : Tcenv.env -> list<formula> -> list<formula> -> bool
