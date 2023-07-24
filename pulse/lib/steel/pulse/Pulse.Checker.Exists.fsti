module Pulse.Checker.Exists

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

val check_elim_exists
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (t:st_term{Tm_ElimExists? t.term})
  : T.Tac (checker_result_t g pre post_hint)

let intro_exists_witness_singleton (st:st_term)  = 
  match st.term with
  | Tm_IntroExists { witnesses = [_] } -> true
  | _ -> false

let intro_exists_vprop (st:st_term { Tm_IntroExists? st.term })  = 
  match st.term with
  | Tm_IntroExists { p } -> p

val check_intro_exists
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (st:st_term { intro_exists_witness_singleton st })
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) tm_vprop))
  : T.Tac (checker_result_t g pre post_hint)
