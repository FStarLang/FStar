module Pulse.Checker.Common
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

val force_st (#f:_) (#g:_) (#t:_) (#pre:term)
             (pre_typing:tot_typing f g pre Tm_VProp)
             (_:(c:comp { stateful_comp c ==> comp_pre c == pre } & 
                 st_typing f g t c))
  : T.Tac (c:comp_st { comp_pre c == pre } &
           st_typing f g t c)

type check_t =
  f:RT.fstar_top_env ->
  g:env ->
  t:st_term ->
  pre:term ->
  pre_typing:tot_typing f g pre Tm_VProp ->
  post_hint:option term ->
  T.Tac (t:st_term &
         c:comp{stateful_comp c ==> comp_pre c == pre} &
         st_typing f g t c)
