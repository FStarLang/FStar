(*
   Copyright 2023 Microsoft Research

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

module Pulse.Checker.Pure
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Readback

let push_context (ctx:string) (r:range) (g:env) : (g':env { g == g' })
  = push_context g ctx r

val instantiate_term_implicits
  (g:env) (t:term) (expected: option typ)
  (inst_extra : bool) (* Should this instantiate implicits at the end of t? *)
  : T.Tac (term & term)

val instantiate_term_implicits_uvs (g:env) (t:term)
    (inst_extra : bool) (* Should this instantiate implicits at the end of t? *)
  : T.Tac (uvs:env { disjoint g uvs } & term & term)  // uvs

val check_universe (g:env) (t:term)
  : T.Tac (u:universe & universe_of g t u)

val compute_term_type (g:env) (t:term)
  : T.Tac (t:term &
           eff:T.tot_or_ghost &
           ty:term &
           typing g t eff ty)

val compute_term_type_and_u (g:env) (t:term)
  : T.Tac (t:term  &
           eff:T.tot_or_ghost &
           ty:term &
           (u:universe & universe_of g ty u) &
           typing g t eff ty)

val check_term (g:env) (e:term) (eff:T.tot_or_ghost) (t:term)
  : T.Tac (e:term & typing g e eff t)

val check_term_at_type (g:env) (e:term) (t:term)
  : T.Tac (e:term & eff:T.tot_or_ghost & typing g e eff t)

val tc_term_phase1 (g:env) (t:term) (must_tot:bool) : T.Tac (term & term)
val tc_term_phase1_with_type (g: env) (t:term) (must_tot:bool) (expected_typ: term) : T.Tac term
val tc_type_phase1 (g: env) (t: term) (must_tot: bool) : T.Tac (term & universe)

val core_compute_term_type (g:env) (t:term)
  : T.Tac (eff:T.tot_or_ghost &
           ty:term &
           typing g t eff ty)

val core_check_term (g:env) (e:term) (eff:T.tot_or_ghost) (t:term)
  : T.Tac (typing g e eff t)

val core_check_term_at_type (g:env) (e:term) (t:term)
  : T.Tac (eff:T.tot_or_ghost & typing g e eff t)

val check_slprop (g:env)
                (t:term)
  : T.Tac (t:term & tot_typing g t tm_slprop)

val check_slprop_with_core (g:env)
                          (t:term)
  : T.Tac (tot_typing g t tm_slprop)

val try_get_non_informative_witness (g:env) (u:universe) (t:term)
  (t_typing:universe_of g t u)
  : T.Tac (option (non_informative_t g u t))

val get_non_informative_witness (g:env) (u:universe) (t:term)
  (t_typing:universe_of g t u)
  : T.Tac (non_informative_t g u t)

val try_check_prop_validity (g:env) (p:term) (_:tot_typing g p tm_prop)
  : T.Tac (option (Pulse.Typing.prop_validity g p))

val check_prop_validity (g:env) (p:term) (_:tot_typing g p tm_prop)
  : T.Tac (Pulse.Typing.prop_validity g p)

val compute_tot_term_type (g:env) (t:term)
  : T.Tac (t:term & ty:typ & tot_typing g t ty)

val compute_tot_term_type_and_u (g:env) (t:term)
  : T.Tac (t:term &
           u:universe &
           ty:typ &
           universe_of g ty u &
           tot_typing g t ty)

val check_tot_term (g:env) (e:term) (t:term)
  : T.Tac (e:term &
           tot_typing g e t)

val core_compute_tot_term_type (g:env) (t:term)
  : T.Tac (ty:typ &
           tot_typing g t ty)

val core_check_tot_term (g:env) (e:term) (t:typ)
  : T.Tac (tot_typing g e t)

val is_non_informative (g:env) (c:comp)
  : T.Tac (option (T.non_informative_token (elab_env g) (elab_comp c)))

val check_subtyping (g:env) (t1 t2 : term)
  : T.Tac (subtyping_token g t1 t2)


val norm_well_typed_term
  (g:T.env) (steps : list norm_step) (t:term)
: T.Tac (t':term{T.equiv_token g t t'})
module RT = FStar.Reflection.Typing

val norm_well_typed_term_alt
      (#g:T.env)
      (#t:T.term)
      (#eff:T.tot_or_ghost)
      (#k:Ghost.erased T.term)
      (ty:Ghost.erased (RT.typing g t (eff, Ghost.reveal k)))
      (steps:list norm_step)
: T.Tac (
      t':T.term &
      Ghost.erased (RT.typing g t' (eff, Ghost.reveal k)) &
      Ghost.erased (RT.related g t RT.R_Eq t')
    )