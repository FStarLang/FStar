module Pulse.Checker.Bind
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Common

val check_bind
  (g:env)
  (t:st_term{Tm_Bind? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (frame_pre:bool)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint frame_pre)

val check_tot_bind
  (g:env)
  (t:st_term{Tm_TotBind? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (frame_pre:bool)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint frame_pre)

