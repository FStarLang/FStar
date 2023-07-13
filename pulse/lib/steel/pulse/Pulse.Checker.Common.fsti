module Pulse.Checker.Common
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
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

exception Framing_failure of Pulse.Checker.Framing.framing_failure

val try_frame_pre (#g:env)
                  (#t:st_term)
                  (#pre:term)
                  (pre_typing: tot_typing g pre tm_vprop)
                  (#c:comp_st)
                  (t_typing: st_typing g t c)
  : T.Tac (c':comp_st { comp_pre c' == pre } &
           st_typing g t c')

type checker_result_t (g:env) (ctxt:term) (post_hint:option post_hint_t) (frame_pre:bool) =
    t:st_term &
    c:comp{(stateful_comp c /\ frame_pre) ==> (comp_pre c == ctxt /\ comp_post_matches_hint c post_hint) } &
    st_typing g t c

type check_t =
  g:env ->
  t:st_term ->
  pre:term ->
  pre_typing:tot_typing g pre tm_vprop ->
  post_hint:post_hint_opt g ->
  frame_pre:bool ->
  T.Tac (checker_result_t g pre post_hint frame_pre)

val repack (#g:env) (#pre:term) (#t:st_term)
           (x:(c:comp_st { comp_pre c == pre } & st_typing g t c))
           (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint true)

val intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) tm_vprop)
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) tm_vprop)
  : T.Tac (comp_typing g c (comp_u c))
