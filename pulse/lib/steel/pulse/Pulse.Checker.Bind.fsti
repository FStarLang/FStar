module Pulse.Checker.Bind

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

val check_bind
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_Bind? t.term})
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)

val check_tot_bind
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_TotBind? t.term })
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)
