module Pulse.Checker.AssertWithBinders

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common


// val check
//   (g:env)
//   (st:st_term{Tm_ProofHintWithBinders? st.term})
//   (pre:term)
//   (pre_typing:tot_typing g pre tm_vprop)
//   (post_hint:post_hint_opt g)
//   (frame_pre:bool)
//   (check:check_t)
//   : T.Tac (checker_result_t g pre post_hint frame_pre)
