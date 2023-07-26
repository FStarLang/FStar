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

val format_failed_goal (g:env) (ctxt:list term) (goal:list term) : T.Tac string

val intro_post_hint (g:env) (ctag_opt:option ctag) (ret_ty:option term) (post:term)
  : T.Tac (post_hint_for_env g)

val post_hint_from_comp_typing (#g:env) (#c:comp_st) (ct:Metatheory.comp_typing_u g c)
  : post_hint_for_env g

type continuation_elaborator
  (g:env)                         (ctxt:vprop)
  (g':env { g' `env_extends` g }) (ctxt':vprop) =

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
  (d1:vprop_equiv g1 ctxt1 ctxt1')
  (d2:vprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2'

//
// A canonical continuation elaborator for Bind
//
val continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_vprop)
  (x:nvar { None? (lookup g (snd x)) })
  : T.Tac (continuation_elaborator
             g
             (tm_star ctxt (comp_pre c1))
             (push_binding g (snd x) (fst x) (comp_res c1))
             (tm_star (open_term (comp_post c1) (snd x)) ctxt))

val continuation_elaborator_with_tot_bind (#g:env) (#ctxt:term)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
  (#e1:term)
  (#t1:term)
  (e1_typing:tot_typing g e1 t1)
  (x:nvar { None? (lookup g (snd x)) })
  : T.Tac (continuation_elaborator
           g ctxt
           (push_binding g (snd x) ppname_default t1) ctxt)

val check_equiv_emp (g:env) (vp:term)
  : option (vprop_equiv g vp tm_emp)

let checker_res_matches_post_hint
  (g:env)
  (post_hint:post_hint_opt g)
  (x:var) (t:term) (ctxt':vprop) =

  match post_hint with
  | None -> True
  | Some post_hint ->
    t == post_hint.ret_ty /\
    ctxt' == open_term post_hint.post x

let checker_result_inv (g:env) (post_hint:post_hint_opt g)
  (x:var)
  (g1:env)
  (t:(u:universe & t:term & universe_of g1 t u))
  (ctxt':(ctxt':vprop & tot_typing g1 ctxt' tm_vprop)) =

  let (| _, t, _ |) = t in
  let (| ctxt', _ |) = ctxt' in
  checker_res_matches_post_hint g post_hint x t ctxt' /\
  lookup g1 x == Some t

//
// x is the variable in which the result of the checked computation is bound
// t is the type of the checked computation
//
type checker_result_t (g:env) (ctxt:vprop) (post_hint:post_hint_opt g) =
  x:var &
  g1:env { g1 `env_extends` g } &
  t:(u:universe & t:typ & universe_of g1 t u) &
  ctxt':(ctxt':vprop & tot_typing g1 ctxt' tm_vprop) &
  k:continuation_elaborator g ctxt g1 (dfst ctxt') {
    checker_result_inv g post_hint x g1 t ctxt'
  }

type check_t =
  g:env ->
  ctxt:vprop ->
  ctxt_typing:tot_typing g ctxt tm_vprop ->
  post_hint:post_hint_opt g ->
  res_ppname:ppname ->
  t:st_term ->
  T.Tac (checker_result_t g ctxt post_hint)
  
val intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) tm_vprop)
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) tm_vprop)
  : T.Tac (comp_typing g c (comp_u c))

val apply_checker_result_k (#g:env) (#ctxt:vprop) (#post_hint:post_hint_for_env g)
  (r:checker_result_t g ctxt (Some post_hint))
  : T.Tac (st_typing_in_ctxt g ctxt (Some post_hint))

val checker_result_for_st_typing (#g:env) (#ctxt:vprop) (#post_hint:post_hint_opt g)
  (d:st_typing_in_ctxt g ctxt post_hint)
  (ppname:ppname)
  : T.Tac (checker_result_t g ctxt post_hint)
