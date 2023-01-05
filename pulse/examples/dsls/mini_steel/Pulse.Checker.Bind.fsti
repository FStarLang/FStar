module Pulse.Checker.Bind
module RT = Refl.Typing
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
               (t:term{Tm_Bind? t})
               (pre:pure_term)
               (pre_typing:tot_typing f g pre Tm_VProp)
               (post_hint:option term)
               (check:check_t)
  : T.Tac (t:term &
           c:pure_comp { C_ST? c ==> comp_pre c == pre } &
           src_typing f g t c)
