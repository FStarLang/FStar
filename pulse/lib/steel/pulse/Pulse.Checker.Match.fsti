module Pulse.Checker.Match

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

module T = FStar.Tactics.V2

val check
        (g:env)
        (pre:term)
        (pre_typing: tot_typing g pre tm_vprop)
        (post_hint:post_hint_for_env g)
        (res_ppname:ppname)
        (sc:term)
        (brs:list branch)
        (check:check_t)
  : T.Tac (checker_result_t g pre (Some post_hint))
