module Pulse.Checker.Admit

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

val check_admit
  (g:env)
  (t:st_term { Tm_Admit? t.term })
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint)
