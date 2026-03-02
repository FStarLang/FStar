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
module FStarC.Reflection.V1.Builtins

open FStarC
open FStarC.Effect
open FStarC.Order
open FStarC.Reflection.V1.Data
open FStarC.Syntax.Embeddings
open FStarC.Syntax.Syntax
open FStarC.VConfig
open FStarC.Ident

module Env = FStarC.TypeChecker.Env
module RD  = FStarC.Reflection.V1.Data

(* Views *)
val inspect_aqual  : aqual -> aqualv
val pack_aqual     : aqualv -> ML aqual

val inspect_fv    : fv -> ML (list string)
val pack_fv       : list string -> ML fv

val inspect_const : sconst -> ML vconst

val inspect_universe : universe -> universe_view
val pack_universe    : universe_view -> universe

val inspect_ln    : term -> ML term_view

val inspect_comp  : comp -> ML comp_view
val pack_comp     : comp_view -> ML comp

val pack_const    : vconst -> ML sconst
val pack_ln       : term_view -> ML term

(* Primitives *)
val compare_bv            : bv -> bv -> ML order
val lookup_attr           : term -> Env.env -> ML (list fv)
val all_defs_in_env       : Env.env -> ML (list fv)
val defs_in_module        : Env.env -> name -> ML (list fv)
val lookup_typ            : Env.env -> list string -> ML (option sigelt)

val sigelt_attrs     : sigelt -> list attribute
val set_sigelt_attrs : list attribute -> sigelt -> sigelt

val sigelt_quals     : sigelt -> ML (list RD.qualifier)
val set_sigelt_quals : list RD.qualifier -> sigelt -> ML sigelt

val sigelt_opts           : sigelt -> option vconfig
val embed_vconfig         : vconfig -> ML term

val inspect_sigelt : sigelt -> ML sigelt_view
val pack_sigelt    : sigelt_view -> ML sigelt

val inspect_lb     : letbinding -> ML lb_view
val pack_lb        : lb_view -> ML letbinding

val inspect_bv     : bv -> ML bv_view
val pack_bv        : bv_view -> ML bv

val inspect_binder : binder -> ML binder_view
val pack_binder    : binder_view -> ML binder

val moduleof              : Env.env -> ML (list string)
val env_open_modules      : Env.env -> ML (list name)
val binders_of_env        : Env.env -> ML binders

val term_eq               : term -> term -> ML bool

(* We're only taking these as primitives to break the dependency from *
FStarC.Tactics into FStar.String, which pulls a LOT of modules. *)
val implode_qn     : list string -> string
val explode_qn     : string -> list string
val compare_string : string -> string -> int

val push_binder    : Env.env -> binder -> ML Env.env

val subst          : bv -> term -> term -> ML term
val close_term     : binder -> term -> ML term

val range_of_term : term -> FStarC.Range.t
val range_of_sigelt : sigelt -> FStarC.Range.t
