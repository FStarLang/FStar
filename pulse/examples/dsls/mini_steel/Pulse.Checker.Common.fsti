module Pulse.Checker.Common
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

val force_st (#f:_) (#g:_) (#t:_) (#pre:pure_term)
  (pre_typing:tot_typing f g pre Tm_VProp)
  (x:(c:pure_comp { stateful_comp c ==> comp_pre c == pre } & 
      src_typing f g t c))
  : T.Tac (c:pure_comp_st { comp_pre c == pre } &
           src_typing f g t c)

type check_t =
  f:RT.fstar_top_env ->
  g:env ->
  t:term ->
  pre:pure_term ->
  pre_typing:tot_typing f g pre Tm_VProp ->
  post_hint:option term ->
  T.Tac (t:term &
         c:pure_comp{stateful_comp c ==> comp_pre c == pre} &
         src_typing f g t c)
