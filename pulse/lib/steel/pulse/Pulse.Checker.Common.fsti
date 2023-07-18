module Pulse.Checker.Common
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

// let mk_abs ty t = RT.(mk_abs (elab_term ty) T.Q_Explicit (elab_term t))
// let mk_arrow ty t = RT.mk_arrow (elab_term ty) T.Q_Explicit (elab_term t)

val intro_post_hint (g:env) (ret_ty:option term) (post:term)
  : T.Tac (post_hint_for_env g)

val post_hint_from_comp_typing (#g:env) (#c:comp_st) (ct:Metatheory.comp_typing_u g c)
  : post_hint_for_env g

// exception Framing_failure of Pulse.Checker.Framing.framing_failure

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
  (x:var { None? (lookup g x) })
  : T.Tac (continuation_elaborator
             g                                (tm_star ctxt (comp_pre c1))
             (push_binding g x ppname_default (comp_res c1)) (tm_star (open_term (comp_post c1) x) ctxt))

val check_equiv_emp (g:env) (vp:term)
  : option (vprop_equiv g vp tm_emp)

let checker_res_matches_post_hint
  (g:env)
  (post_hint:post_hint_opt g)
  (x:var) (t:term) (ctxt':vprop) = x_t_ctxt_match_post_hint g post_hint x t ctxt'

type checker_result_t (g:env) (ctxt:vprop) (post_hint:post_hint_opt g) =
  x:var &
  t:term &
  ctxt':vprop { checker_res_matches_post_hint g post_hint x t ctxt' } &
  g1:env { g1 `env_extends` g /\ lookup g1 x == Some t } &
  continuation_elaborator g ctxt g1 ctxt'

type check_t =
  g:env ->
  ctxt:vprop ->
  ctxt_typing:tot_typing g ctxt tm_vprop ->
  post_hint:post_hint_opt g ->
  t:st_term ->
  T.Tac (checker_result_t g ctxt post_hint)
  
val intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) tm_vprop)
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) tm_vprop)
  : T.Tac (comp_typing g c (comp_u c))
