module Pulse.Checker.Match

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

val check_match
        (g:env)
        (sc:term)
        (brs:list branch)
        (pre:term)
        (pre_typing: tot_typing g pre tm_vprop)
        (post_hint:post_hint_for_env g)
        (check:check_t)
  : T.Tac (checker_result_t g pre (Some post_hint))
