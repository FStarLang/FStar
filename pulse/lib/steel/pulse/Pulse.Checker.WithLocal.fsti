module Pulse.Checker.WithLocal

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

val check_withlocal
  (g:env)
  (t:st_term { Tm_WithLocal? t.term })
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)
