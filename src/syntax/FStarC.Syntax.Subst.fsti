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
module FStarC.Syntax.Subst
open FStarC.Effect

open FStarC
open FStarC.Syntax
open FStarC.Syntax.Syntax

val compress_univ:      universe -> ML universe
val subst':             subst_ts -> term -> ML term
val shift_subst:        int -> subst_t -> ML subst_t
val subst_binder:       list subst_elt -> binder -> ML binder
val subst_binders:      list subst_elt -> binders -> ML binders

//
// It pushes delayed substitutions down,
//   but does not resolve uvars
//
// Whereas compress does both
//
val compress_subst: term -> ML term

val compress:           term -> ML term
val subst:              list subst_elt -> term -> ML term
val set_use_range: Range.Type.range -> term -> ML term
val subst_comp:         list subst_elt -> comp -> ML comp
val subst_bqual:        list subst_elt -> bqual -> ML bqual
val subst_aqual:        list subst_elt -> aqual -> ML aqual
val subst_ascription:   list subst_elt -> ascription -> ML ascription
val subst_decreasing_order:
                        list subst_elt -> decreases_order -> ML decreases_order
val subst_residual_comp:list subst_elt -> residual_comp -> ML residual_comp
val open_binders':      binders -> ML (binders & subst_t)
val open_binders:       binders -> ML binders
val open_term':         binders -> term -> ML (binders & term & subst_t)
val open_term:          binders -> term -> ML (binders & term)
val open_comp:          binders -> comp -> ML (binders & comp)
val open_ascription:    binders -> ascription -> ML (binders & ascription)
val open_branch':       branch -> ML (branch & subst_t)
val open_branch:        branch -> ML branch
val close:                binders -> term -> ML term
val close_comp:           binders -> comp -> ML comp
val close_binders:        binders -> ML binders
val close_ascription:     binders -> ascription -> ML ascription
val close_branch:         branch -> ML branch
val univ_var_opening: univ_names -> ML (list subst_elt & list univ_name)
val univ_var_closing: univ_names -> ML (list subst_elt)
val open_univ_vars:     univ_names -> term -> ML (univ_names & term)
val open_univ_vars_comp:univ_names -> comp -> ML (univ_names & comp)
val close_univ_vars:      univ_names -> term -> ML term
val close_univ_vars_comp: univ_names -> comp -> ML comp
val open_let_rec:       list letbinding -> term -> ML (list letbinding & term)
val close_let_rec:        list letbinding -> term -> ML (list letbinding & term)
val close_tscheme: binders -> tscheme -> ML tscheme
val close_univ_vars_tscheme: univ_names -> tscheme -> ML tscheme
val subst_tscheme: list subst_elt -> tscheme -> ML tscheme
val opening_of_binders: binders -> ML subst_t
val closing_of_binders:   binders -> ML subst_t

(* Helpers *)
val open_term_1   : binder   -> term -> ML (binder & term)
val open_term_bvs : list bv -> term -> ML (list bv & term)
val open_term_bv  : bv       -> term -> ML (bv & term)
