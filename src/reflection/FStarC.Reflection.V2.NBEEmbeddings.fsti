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

module FStarC.Reflection.V2.NBEEmbeddings

open FStarC
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.NBETerm
open FStarC.Reflection.V2.Data
module RD = FStarC.Reflection.V2.Data

(* Embeddings *)
val e_bv            : embedding bv
val e_namedv        : embedding namedv
instance val e_binder        : embedding binder
instance val e_binder_view   : embedding binder_view
instance val e_binders       : embedding binders
instance val e_binding       : embedding RD.binding
instance val e_term          : embedding term
instance val e_term_view     : embedding term_view
instance val e_fv            : embedding fv
instance val e_comp          : embedding FStarC.Syntax.Syntax.comp
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
instance val e_bv_view       : embedding bv_view
instance val e_namedv_view   : embedding namedv_view
instance val e_attribute     : embedding attribute
instance val e_attributes    : embedding (list attribute) (* This seems rather silly, but `attributes` is a keyword *)
instance val e_qualifier     : embedding RD.qualifier
instance val e_qualifiers    : embedding (list RD.qualifier)
instance val e_ident         : embedding Ident.ident
instance val e_univ_name     : embedding univ_name
instance val e_univ_names    : embedding (list univ_name)
instance val e_universe      : embedding universe
instance val e_universe_view : embedding universe_view
instance val e_subst_elt     : embedding subst_elt
instance val e_subst         : embedding (list subst_elt)
