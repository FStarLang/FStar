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

open FStarC.Compiler
open FStarC.Compiler.Effect
open FStarC.Compiler.Order
open FStarC.Reflection.V2.Data
open FStarC.Syntax.Embeddings
open FStarC.Syntax.Syntax
open FStarC.VConfig
open FStarC.Ident

module EMB = FStarC.Syntax.Embeddings
module Env = FStarC.TypeChecker.Env
module O   = FStarC.Options
module RD  = FStarC.Reflection.V2.Data
module S   = FStarC.Syntax.Syntax
module Z   = FStarC.BigInt

(* Primitives *)
val compare_bv            : bv -> bv -> order
val compare_namedv        : namedv -> namedv -> order
val lookup_typ            : Env.env -> list string -> option sigelt
val lookup_attr_ses       : term -> Env.env -> list sigelt
val lookup_attr           : term -> Env.env -> list fv
val all_defs_in_env       : Env.env -> list fv
val defs_in_module        : Env.env -> name -> list fv
val vars_of_env           : Env.env -> list RD.binding
val moduleof              : Env.env -> list string
val term_eq               : term -> term -> bool
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

val inspect_namedv : namedv -> namedv_view
val pack_namedv    : namedv_view -> namedv

val inspect_bv     : bv -> bv_view
val pack_bv        : bv_view -> bv

val inspect_binder : binder -> binder_view
val pack_binder    : binder_view -> binder

val inspect_aqual  : aqual -> aqualv
val pack_aqual     : aqualv -> aqual

val inspect_universe : universe -> universe_view
val pack_universe    : universe_view -> universe

(* Only used internally by check_match_complete... the pattern
(abstract) type is not really exposed, so the user has no use for these.
Perhaps it is more consistent to introduce a pattern_view... *)
val inspect_pat   : S.pat -> pattern
val pack_pat      : pattern -> S.pat

(* We're only taking these as primitives to break the dependency from *
FStarC.Tactics into FStar.String, which pulls a LOT of modules. *)
val implode_qn     : list string -> string
val explode_qn     : string -> list string
val compare_string : string -> string -> Z.t

val push_namedv    : Env.env -> bv     -> Env.env

val range_of_term : term -> Range.range
val range_of_sigelt : sigelt -> Range.range

val subst_term : list subst_elt -> term -> term
val subst_comp : list subst_elt -> comp -> comp

val inspect_ident : ident -> string & Range.range
val pack_ident : string & Range.range -> ident
