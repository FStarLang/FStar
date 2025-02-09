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
module FStarC.Reflection.V2.Embeddings

open FStarC
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStar.Order
open FStarC.TypeChecker.Env
open FStarC.Reflection.V2.Data
module RD = FStarC.Reflection.V2.Data

(* FIXME: create a Reflection.Types module internally? *)
type namedv = bv

(* Embeddings *)
val e_bv            : embedding bv
val e_namedv        : embedding namedv
(* Sadly these two cannot be instances: they are the same type! *)
instance val e_binding       : embedding RD.binding
instance val e_binder        : embedding binder
instance val e_binder_view   : embedding binder_view
instance val e_binders       : embedding binders
(* not instance *) val e_term          : embedding term
instance val e_term_view     : embedding term_view
instance val e_fv            : embedding fv
instance val e_comp          : embedding comp
instance val e_comp_view     : embedding comp_view
instance val e_vconst        : embedding vconst
instance val e_env           : embedding FStarC.TypeChecker.Env.env
instance val e_pattern       : embedding pattern
instance val e_branch        : embedding Data.branch
instance val e_aqualv        : embedding aqualv
instance val e_argv          : embedding argv
instance val e_sigelt        : embedding sigelt
instance val e_letbinding    : embedding letbinding
instance val e_lb_view       : embedding lb_view
instance val e_sigelt_view   : embedding sigelt_view
instance val e_namedv_view   : embedding namedv_view
instance val e_bv_view       : embedding bv_view
         val e_attribute     : embedding attribute
instance val e_qualifier     : embedding RD.qualifier
instance val e_ident         : embedding Ident.ident
instance val e_univ_name     : embedding univ_name
instance val e_universe      : embedding universe
instance val e_universe_view : embedding universe_view
instance val e_subst_elt     : embedding subst_elt

(* Useful for embedding antiquoted terms. They are only used for the embedding part,
 * so this is a bit hackish. *)
val e_term_aq       : antiquotations -> embedding term
val e_term_view_aq  : antiquotations -> embedding term_view

(* Lazy unfoldings *)
val unfold_lazy_bv     : lazyinfo -> term
val unfold_lazy_namedv : lazyinfo -> term
val unfold_lazy_fvar   : lazyinfo -> term
val unfold_lazy_binder : lazyinfo -> term
val unfold_lazy_optionstate : lazyinfo -> term
val unfold_lazy_comp   : lazyinfo -> term
val unfold_lazy_env    : lazyinfo -> term
val unfold_lazy_sigelt : lazyinfo -> term
val unfold_lazy_letbinding : lazyinfo -> term
val unfold_lazy_universe   : lazyinfo -> term
val unfold_lazy_doc        : lazyinfo -> term
