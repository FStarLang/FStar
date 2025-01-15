(*
   Copyright 2008-2022 Microsoft Research

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

module FStarC.Reflection.V1.NBEEmbeddings

open FStar open FStarC
open FStarC
open FStarC.TypeChecker.NBETerm
open FStarC.Syntax.Syntax
open FStar.Order
open FStarC.TypeChecker.Env
open FStarC.Reflection.V1.Data
module RD = FStarC.Reflection.V1.Data
module S = FStarC.Syntax.Syntax

(* Embeddings. We mark the ones proper to this module as instances *)
instance val e_aqualv        : embedding aqualv
instance val e_binder_view   : embedding binder_view
instance val e_branch        : embedding Data.branch
instance val e_bv_view       : embedding bv_view
instance val e_comp_view     : embedding comp_view
instance val e_const         : embedding vconst
instance val e_lb_view       : embedding lb_view
instance val e_pattern       : embedding pattern
instance val e_qualifier     : embedding RD.qualifier
instance val e_sigelt_view   : embedding sigelt_view
instance val e_term_view     : embedding term_view
instance val e_universe_view : embedding universe_view
val e_argv          : embedding argv
val e_attribute     : embedding attribute
val e_attributes    : embedding (list attribute) (* This seems rather silly, but `attributes` is a keyword *)
val e_binder        : embedding binder
val e_binders       : embedding binders
val e_bv            : embedding bv
val e_comp          : embedding S.comp
val e_env           : embedding FStarC.TypeChecker.Env.env
val e_fv            : embedding fv
val e_ident         : embedding RD.ident (* NOT FStarC.Ident.ident *)
val e_letbinding    : embedding letbinding
val e_qualifiers    : embedding (list RD.qualifier)
val e_sigelt        : embedding sigelt
val e_term          : embedding S.term
val e_univ_name     : embedding RD.univ_name (* NOT Syntax.univ_name *)
val e_univ_names    : embedding (list RD.univ_name) (* NOT Syntax.univ_name *)
val e_universe      : embedding universe
