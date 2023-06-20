module Pulse.Checker.Return

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common

val check_return
  (allow_inst:bool)
  (g:env)
  (st:st_term{Tm_Return? st.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint)