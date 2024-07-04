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

module Pulse.Checker.Base

module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
module FV = Pulse.Typing.FV
module RU = Pulse.RuntimeUtils
module Metatheory = Pulse.Typing.Metatheory

val debug (g:env) (f:unit -> T.Tac string) : T.Tac unit

val format_failed_goal (g:env) (ctxt:list term) (goal:list term) : T.Tac string

val intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) tm_slprop)
                      (iname_typing:effect_annot_typing g (effect_annot_of_comp c))
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) tm_slprop)
  : T.Tac (comp_typing g c (universe_of_comp c))

val post_typing_as_abstraction
  (#g:env) (#x:var) (#ty:term) (#t:term { fresh_wrt x g (freevars t) })
  (_:tot_typing (push_binding g x ppname_default ty) (open_term t x) tm_slprop)
  : FStar.Ghost.erased (RT.tot_typing (elab_env g)
                             (RT.mk_abs ty T.Q_Explicit t)
                             (RT.mk_arrow ty T.Q_Explicit tm_slprop))

let effect_annot_labels_match (a1 a2:effect_annot) =
  match a1, a2 with
  | EffectAnnotAtomic _, EffectAnnotAtomic _
  | EffectAnnotGhost _, EffectAnnotGhost _
  | EffectAnnotAtomicOrGhost _, EffectAnnotAtomicOrGhost _
  | EffectAnnotSTT, EffectAnnotSTT -> True
  | _ -> False

val intro_post_hint
  (g:env)
  (effect_annot:effect_annot)
  (ret_ty:option term)
  (post:term)
  : T.Tac (h:post_hint_for_env g {effect_annot_labels_match h.effect_annot effect_annot})

val post_hint_from_comp_typing (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
  : post_hint_for_env g

val comp_typing_from_post_hint
    (#g: env)
    (c: comp_st)
    (pre_typing: tot_typing g (comp_pre c) tm_slprop)
    (p:post_hint_for_env g { comp_post_matches_hint c (Some p) })
: T.Tac (comp_typing_u g c)

val extend_post_hint (g:env) (p:post_hint_for_env g)
                     (x:var{ None? (lookup g x) }) (tx:term)
                     (conjunct:term) (_:tot_typing (push_binding g x ppname_default tx) conjunct tm_slprop)
  : T.Tac (q:post_hint_for_env (push_binding g x ppname_default tx) {
            q.post == tm_star p.post conjunct /\
            q.ret_ty == p.ret_ty /\
            q.u == p.u /\
            q.effect_annot == p.effect_annot
          })
  

type continuation_elaborator
  (g:env)                         (ctxt:slprop)
  (g':env { g' `env_extends` g }) (ctxt':slprop) =

  post_hint:post_hint_opt g ->
  st_typing_in_ctxt g' ctxt' post_hint ->
  T.Tac (st_typing_in_ctxt g ctxt post_hint)

val k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt

val k_elab_trans
  (#g0:env) (#g1:env { g1 `env_extends` g0 }) (#g2:env { g2 `env_extends` g1 }) (#ctxt0 #ctxt1 #ctxt2:term)
  (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
  (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2

val k_elab_equiv
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)
  (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
  (d1:slprop_equiv g1 ctxt1 ctxt1')
  (d2:slprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2'

//
// A canonical continuation elaborator for Bind
//
val continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_slprop)
  (x:nvar { None? (lookup g (snd x)) })
  : T.Tac (continuation_elaborator
             g
             (tm_star ctxt (comp_pre c1))
             (push_binding g (snd x) (fst x) (comp_res c1))
             (tm_star (open_term (comp_post c1) (snd x)) ctxt))

val continuation_elaborator_with_bind_fn (#g:env) (#ctxt:term)
  (ctxt_typing:tot_typing g ctxt tm_slprop)
  (#e1:st_term)
  (#c1:comp { C_Tot? c1 })
  (b:binder{b.binder_ty == comp_res c1})
  (e1_typing:st_typing g e1 c1)
  (x:nvar { None? (lookup g (snd x)) })
: T.Tac (continuation_elaborator
          g ctxt
          (push_binding g (snd x) ppname_default (comp_res c1)) ctxt)

val check_equiv_emp (g:env) (vp:term)
  : option (slprop_equiv g vp tm_emp)

let checker_res_matches_post_hint
  (g:env)
  (post_hint:post_hint_opt g)
  (x:var) (t:term) (ctxt':slprop) =

  match post_hint with
  | None -> True
  | Some post_hint ->
    t == post_hint.ret_ty /\
    ctxt' == open_term post_hint.post x

let checker_result_inv (g:env) (post_hint:post_hint_opt g)
  (x:var)
  (g1:env)
  (t:(u:universe & t:term & universe_of g1 t u))
  (ctxt':(ctxt':slprop & tot_typing g1 ctxt' tm_slprop)) =

  let (| _, t, _ |) = t in
  let (| ctxt', _ |) = ctxt' in
  checker_res_matches_post_hint g post_hint x t ctxt' /\
  lookup g1 x == Some t

//
// x is the variable in which the result of the checked computation is bound
// t is the type of the checked computation
//
type checker_result_t (g:env) (ctxt:slprop) (post_hint:post_hint_opt g) =
  x:var &
  g1:env { g1 `env_extends` g } &
  t:(u:universe & t:typ & universe_of g1 t u) &
  ctxt':(ctxt':slprop & tot_typing g1 ctxt' tm_slprop) &
  k:continuation_elaborator g ctxt g1 (dfst ctxt') {
    checker_result_inv g post_hint x g1 t ctxt'
  }

type check_t =
  g:env ->
  ctxt:slprop ->
  ctxt_typing:tot_typing g ctxt tm_slprop ->
  post_hint:post_hint_opt g ->
  res_ppname:ppname ->
  t:st_term ->
  T.Tac (checker_result_t g ctxt post_hint)
  
val match_comp_res_with_post_hint (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (post_hint:post_hint_opt g)
  : T.Tac (t':st_term &
           c':comp_st &
           st_typing g t' c')

val apply_checker_result_k (#g:env) (#ctxt:slprop) (#post_hint:post_hint_for_env g)
  (r:checker_result_t g ctxt (Some post_hint))
  (res_ppname:ppname)
  : T.Tac (st_typing_in_ctxt g ctxt (Some post_hint))

val checker_result_for_st_typing (#g:env) (#ctxt:slprop) (#post_hint:post_hint_opt g)
  (d:st_typing_in_ctxt g ctxt post_hint)
  (ppname:ppname)
  : T.Tac (checker_result_t g ctxt post_hint)

val is_stateful_application (g:env) (e:term) 
  : T.Tac (option st_term)

val norm_typing
      (g:env) (e:term) (eff:_) (t0:term)
      (d:typing g e eff t0)
      (steps:list norm_step)
  : T.Tac (t':term & typing g e eff t')

val norm_typing_inverse
      (g:env) (e:term) (eff:_) (t0:term)
      (d:typing g e eff t0)
      (t1:term)
      (#u:_)
      (d1:tot_typing g t1 (tm_type u))
      (steps:list norm_step)
  : T.Tac (option (typing g e eff t1))

val norm_st_typing_inverse
      (#g:env) (#e:st_term) (#t0:term)
      (d:st_typing g e (C_Tot t0))
      (#u:_)
      (t1:term)
      (d1:tot_typing g t1 (tm_type u))
      (steps:list norm_step)
  : T.Tac (option (st_typing g e (C_Tot t1)))
