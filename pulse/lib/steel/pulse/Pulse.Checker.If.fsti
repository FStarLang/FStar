module Pulse.Checker.If

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common

val check_if (g:env)
             (b:term)
             (e1 e2:st_term)
             (pre:term)
             (pre_typing: tot_typing g pre Tm_VProp)
             (post_hint:post_hint_for_env g)
             (check:check_t)
  : T.Tac (checker_result_t g pre (Some post_hint))
