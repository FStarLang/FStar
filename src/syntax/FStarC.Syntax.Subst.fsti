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

val shift_subst:        int -> subst_t -> subst_t
val subst:              list subst_elt -> term -> term
val subst':             subst_ts -> term -> term
val subst_comp:         list subst_elt -> comp -> comp
val subst_bqual:        list subst_elt -> bqual -> bqual
val subst_aqual:        list subst_elt -> aqual -> aqual
val subst_ascription:   list subst_elt -> ascription -> ascription
val subst_decreasing_order:
                        list subst_elt -> decreases_order -> decreases_order
val subst_binder:       list subst_elt -> binder -> binder
val subst_binders:      list subst_elt -> binders -> binders
val subst_residual_comp:list subst_elt -> residual_comp -> residual_comp
val compress:           term -> term
val compress_univ:      universe -> universe

//
// It pushes delayed substitutions down,
//   but does not resolve uvars
//
// Whereas compress does both
//
val compress_subst: term -> term

val close:                binders -> term -> term
val close_comp:           binders -> comp -> comp
val close_binders:        binders -> binders
val close_ascription:     binders -> ascription -> ascription
val close_branch:         branch -> branch
val close_univ_vars:      univ_names -> term -> term
val close_univ_vars_comp: univ_names -> comp -> comp
val close_let_rec:        list letbinding -> term -> list letbinding & term
val closing_of_binders:   binders -> subst_t

val open_binders':      binders -> binders & subst_t
val open_binders:       binders -> binders
val open_term:          binders -> term -> binders & term
val open_term':         binders -> term -> binders & term & subst_t
val open_comp:          binders -> comp -> binders & comp
val open_ascription:    binders -> ascription -> binders & ascription
val open_branch:        branch -> branch
val open_branch':       branch -> branch & subst_t
val open_let_rec:       list letbinding -> term -> list letbinding & term
val open_univ_vars:     univ_names -> term -> univ_names & term
val open_univ_vars_comp:univ_names -> comp -> univ_names & comp
val opening_of_binders: binders -> subst_t

val subst_tscheme: list subst_elt -> tscheme -> tscheme
val close_tscheme: binders -> tscheme -> tscheme
val close_univ_vars_tscheme: univ_names -> tscheme -> tscheme

val univ_var_opening: univ_names -> list subst_elt & list univ_name
val univ_var_closing: univ_names -> list subst_elt

val set_use_range: Range.Type.range -> term -> term

(* Helpers *)
val open_term_1   : binder   -> term -> binder & term
val open_term_bvs : list bv -> term -> list bv & term
val open_term_bv  : bv       -> term -> bv & term
