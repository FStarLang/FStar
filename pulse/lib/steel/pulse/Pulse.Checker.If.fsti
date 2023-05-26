module Pulse.Checker.If

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common

val check_if (g:env)
             (b:term)
             (e1 e2:st_term)
             (pre:term)
             (pre_typing: tot_typing g pre Tm_VProp)
             (post_hint:post_hint_for_env g)
             (check:check_t)
  : T.Tac (t:st_term &
           c:comp { stateful_comp c ==> comp_pre c == pre } &
           st_typing g t c)
