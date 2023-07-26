module Pulse.Checker.If

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

val check
  (g:env)
  (pre:term)
  (pre_typing: tot_typing g pre tm_vprop)
  (post_hint:post_hint_for_env g)
  (res_ppname:ppname)
  (b:term)
  (e1 e2:st_term)
  (check:check_t)
  : T.Tac (checker_result_t g pre (Some post_hint))
