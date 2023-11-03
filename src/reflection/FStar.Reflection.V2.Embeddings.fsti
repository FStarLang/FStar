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
module FStar.Reflection.V2.Embeddings

open FStar open FStar.Compiler
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order
open FStar.TypeChecker.Env
open FStar.Reflection.V2.Data
module O = FStar.Options
module RD = FStar.Reflection.V2.Data

(* FIXME: create a Reflection.Types module internally? *)
type namedv = bv

(* Embeddings *)
val e_bv            : embedding bv
val e_namedv        : embedding namedv
val e_binding       : embedding RD.binding
val e_binder        : embedding binder
val e_binder_view   : embedding binder_view
val e_binders       : embedding binders
val e_term          : embedding term
val e_term_view     : embedding term_view
val e_fv            : embedding fv
val e_comp          : embedding comp
val e_comp_view     : embedding comp_view
val e_vconst        : embedding vconst
val e_env           : embedding FStar.TypeChecker.Env.env
val e_pattern       : embedding pattern
val e_branch        : embedding Data.branch
val e_aqualv        : embedding aqualv
val e_argv          : embedding argv
val e_order         : embedding order
val e_sigelt        : embedding sigelt
val e_letbinding    : embedding letbinding
val e_lb_view       : embedding lb_view
val e_sigelt_view   : embedding sigelt_view
val e_namedv_view   : embedding namedv_view
val e_bv_view       : embedding bv_view
val e_attribute     : embedding attribute
val e_attributes    : embedding (list attribute) (* This seems rather silly, but `attributes` is a keyword *)
val e_qualifier     : embedding RD.qualifier
val e_qualifiers    : embedding (list RD.qualifier)
val e_ident         : embedding Ident.ident
val e_univ_name     : embedding univ_name
val e_univ_names    : embedding (list univ_name)
val e_universe      : embedding universe
val e_universe_view : embedding universe_view
val e_subst_elt     : embedding subst_elt
val e_subst         : embedding (list subst_elt)

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
