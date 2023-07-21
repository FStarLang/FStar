module Pulse.Checker.Bind

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common

val check_bind
  (g:env)
  (t:st_term{Tm_Bind? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)

val check_tot_bind
  (g:env)
  (t:st_term { Tm_TotBind? t.term })
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)

// val check_bindv2
//   (g:env)
//   (t:st_term {Tm_Bind? t.term})
//   (pre:term)
//   (pre_typing:tot_typing g pre tm_vprop)
//   (post_hint:post_hint_opt g)
//   (frame_pre:bool)
//   (check:check_t)
//   : T.Tac (checker_result_t g pre post_hint frame_pre)
