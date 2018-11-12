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
#light "off"
module FStar.Reflection.Basic

open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order
module Env = FStar.TypeChecker.Env
open FStar.Reflection.Data
open FStar.ST

(* Tying a knot into the environment which started execution.
 * Needed to inspect sigelts and the like without needing
 * to explicitly pass it in. This entire module should really be in
 * the TAC effect, and this crap is a symptom, let's move it. *)
val env_hook : ref<option<Env.env>>

(* Primitives *)
val compare_bv     : bv -> bv -> order
val lookup_typ     : Env.env -> list<string> -> option<sigelt>
val is_free        : bv -> term -> bool
val lookup_attr    : term -> Env.env -> list<fv>
val binders_of_env : Env.env -> binders
val moduleof       : Env.env -> list<string>
val term_eq        : term -> term -> bool
val term_to_string : term -> string

val sigelt_attrs     : sigelt -> list<attribute>
val set_sigelt_attrs : list<attribute> -> sigelt -> sigelt

(* Views *)
val inspect_fv    : fv -> list<string>
val pack_fv       : list<string> -> fv

val inspect_const : sconst -> vconst
val pack_const    : vconst -> sconst

val inspect_ln    : term -> term_view
val pack_ln       : term_view -> term

val inspect_comp  : comp -> comp_view
val pack_comp     : comp_view -> comp

val inspect_sigelt : sigelt -> sigelt_view
val pack_sigelt    : sigelt_view -> sigelt

val inspect_bv     : bv -> bv_view
val pack_bv        : bv_view -> bv

val inspect_binder : binder -> bv * aqualv
val pack_binder    : bv -> aqualv -> binder

val inspect_aqual  : aqual -> aqualv
val pack_aqual     : aqualv -> aqual
