module Pulse.Checker.Bind
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Common

val check_bind (f:RT.fstar_top_env)
               (g:env)
               (t:st_term{Tm_Bind? t.term})
               (pre:term)
               (pre_typing:tot_typing f g pre Tm_VProp)
               (post_hint:option term)
               (check:check_t)
  : T.Tac (t:st_term &
           c:comp { stateful_comp c ==> comp_pre c == pre } &
           st_typing f g t c)

val check_tot_bind
  (f:RT.fstar_top_env)
  (g:env)
  (t:st_term{Tm_TotBind? t.term})
  (pre:term)
  (pre_typing:tot_typing f g pre Tm_VProp)
  (post_hint:option term)
  (check:check_t)

  : T.Tac (t:st_term &
           c:comp { stateful_comp c ==> comp_pre c == pre } &
           st_typing f g t c)

