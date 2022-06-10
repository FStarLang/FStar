(*
   Copyright 2008-2015 Microsoft Research

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
module FStar.Reflection.Basic

open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order
module Env = FStar.TypeChecker.Env
open FStar.Reflection.Data
open FStar.Compiler.Effect
module O   = FStar.Options
module RD  = FStar.Reflection.Data
module EMB = FStar.Syntax.Embeddings
module Z   = FStar.BigInt
open FStar.VConfig

(* Primitives *)
val compare_bv            : bv -> bv -> order
val lookup_typ            : Env.env -> list string -> option sigelt
val is_free               : bv -> term -> bool
val free_bvs              : term -> list bv
val free_uvars            : term -> list Z.t
val lookup_attr           : term -> Env.env -> list fv
val all_defs_in_env       : Env.env -> list fv
val defs_in_module        : Env.env -> name -> list fv
val binders_of_env        : Env.env -> binders
val moduleof              : Env.env -> list string
val term_eq               : term -> term -> bool
val term_to_string        : term -> string
val comp_to_string        : comp -> string
val env_open_modules      : Env.env -> list name
val sigelt_opts           : sigelt -> option vconfig
val embed_vconfig         : vconfig -> term

val sigelt_attrs     : sigelt -> list attribute
val set_sigelt_attrs : list attribute -> sigelt -> sigelt

val sigelt_quals     : sigelt -> list RD.qualifier
val set_sigelt_quals : list RD.qualifier -> sigelt -> sigelt

(* Views *)
val inspect_fv    : fv -> list string
val pack_fv       : list string -> fv

val inspect_const : sconst -> vconst
val pack_const    : vconst -> sconst

val inspect_ln    : term -> term_view
val pack_ln       : term_view -> term

val inspect_comp  : comp -> comp_view
val pack_comp     : comp_view -> comp

val inspect_sigelt : sigelt -> sigelt_view
val pack_sigelt    : sigelt_view -> sigelt

val inspect_lb     : letbinding -> lb_view
val pack_lb        : lb_view -> letbinding

val inspect_bv     : bv -> bv_view
val pack_bv        : bv_view -> bv

val inspect_binder : binder -> bv * (aqualv * list term)
val pack_binder    : bv -> aqualv -> list term -> binder

val inspect_aqual  : aqual -> aqualv
val pack_aqual     : aqualv -> aqual

val inspect_universe : universe -> universe_view
val pack_universe    : universe_view -> universe

val subst          : bv -> term -> term -> term
val close_term     : binder -> term -> term

(* We're only taking these as primitives to break the dependency from *
FStar.Tactics into FStar.String, which pulls a LOT of modules. *)
val implode_qn     : list string -> string
val explode_qn     : string -> list string
val compare_string : string -> string -> Z.t

val push_binder    : Env.env -> binder -> Env.env
