module Pulse.Checker.Abs

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common

val check_abs
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (t:st_term &
           c:comp { stateful_comp c ==> comp_pre c == pre } &
           st_typing g t c)
