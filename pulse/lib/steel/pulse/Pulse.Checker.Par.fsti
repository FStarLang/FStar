module Pulse.Checker.Par

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

module T = FStar.Tactics.V2

val check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (t:st_term{Tm_Par? t.term})
  (check:check_t)

  : T.Tac (checker_result_t g pre post_hint)
