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
module FStarC.Reflection.V2.Builtins

open FStarC
open FStarC.Effect
open FStarC.Order
open FStarC.Reflection.V2.Data
open FStarC.Syntax.Embeddings
open FStarC.Syntax.Syntax
open FStarC.VConfig
open FStarC.Ident

module Env = FStarC.TypeChecker.Env
module RD  = FStarC.Reflection.V2.Data
module S   = FStarC.Syntax.Syntax

(* Views *)
val inspect_aqual  : aqual -> aqualv
val pack_aqual     : aqualv -> ML aqual

val inspect_fv    : fv -> ML (list string)
val pack_fv       : list string -> ML fv

val inspect_const : sconst -> ML vconst
val inspect_universe : universe -> universe_view
val pack_universe    : universe_view -> universe

val inspect_pat   : S.pat -> ML pattern
val inspect_ln    : term -> ML term_view

val inspect_comp  : comp -> ML comp_view
val pack_comp     : comp_view -> ML comp

val pack_const    : vconst -> ML sconst
val pack_pat      : pattern -> ML S.pat
val pack_ln       : term_view -> ML term

(* Primitives *)
val compare_bv            : bv -> bv -> ML order
val compare_namedv        : namedv -> namedv -> ML order
val lookup_attr_ses       : term -> Env.env -> ML (list sigelt)
val lookup_attr           : term -> Env.env -> ML (list fv)
val all_defs_in_env       : Env.env -> ML (list fv)
val defs_in_module        : Env.env -> name -> ML (list fv)
val lookup_typ            : Env.env -> list string -> ML (option sigelt)

val sigelt_attrs     : sigelt -> list attribute
val set_sigelt_attrs : list attribute -> sigelt -> sigelt

val syntax_to_rd_qual : S.qualifier -> ML RD.qualifier

val inspect_ident : ident -> string & Range.t
val pack_ident : string & Range.t -> ident

val sigelt_quals     : sigelt -> ML (list RD.qualifier)
val set_sigelt_quals : list RD.qualifier -> sigelt -> ML sigelt

val sigelt_opts           : sigelt -> option vconfig
val embed_vconfig         : vconfig -> ML term

val inspect_sigelt : sigelt -> ML sigelt_view
val pack_sigelt    : sigelt_view -> ML sigelt

val inspect_lb     : letbinding -> ML lb_view
val pack_lb        : lb_view -> ML letbinding

val inspect_namedv : namedv -> ML namedv_view
val pack_namedv    : namedv_view -> ML namedv

val inspect_bv     : bv -> ML bv_view
val pack_bv        : bv_view -> ML bv

val inspect_binder : binder -> ML binder_view
val pack_binder    : binder_view -> ML binder

val moduleof              : Env.env -> ML (list string)
val env_open_modules      : Env.env -> ML (list name)
val vars_of_env           : Env.env -> ML (list RD.binding)
val term_eq               : term -> term -> ML bool

(* We're only taking these as primitives to break the dependency from *
FStarC.Tactics into FStar.String, which pulls a LOT of modules. *)
val implode_qn     : list string -> string
val explode_qn     : string -> list string
val compare_string : string -> string -> int

val push_namedv    : Env.env -> bv     -> ML Env.env

val subst_term : list subst_elt -> term -> ML term
val subst_comp : list subst_elt -> comp -> ML comp

val range_of_term : term -> Range.t
val range_of_sigelt : sigelt -> Range.t
