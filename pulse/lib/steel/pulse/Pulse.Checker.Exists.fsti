module Pulse.Checker.Exists

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common

val check_elim_exists
  (g:env)
  (t:st_term{Tm_ElimExists? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint)

let intro_exists_witness_singleton (st:st_term)  = 
  match st.term with
  | Tm_IntroExists { witnesses = [_] } -> true
  | _ -> false

let intro_exists_vprop (st:st_term { Tm_IntroExists? st.term })  = 
  match st.term with
  | Tm_IntroExists { p } -> p

val check_intro_exists_either
  (g:env)
  (st:st_term{intro_exists_witness_singleton st})
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) Tm_VProp))
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint)