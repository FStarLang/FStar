module Pulse.Checker.AssertWithBinders

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

let head_wild (st:st_term) =
  match st.term with
  | Tm_ProofHintWithBinders { hint_type = WILD } -> true
  | _ -> false

val check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_ProofHintWithBinders? st.term })
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)

