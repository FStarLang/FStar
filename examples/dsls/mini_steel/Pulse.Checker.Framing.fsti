module Pulse.Checker.Framing
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
module P = Pulse.Syntax.Printer

val vprop_as_list (vp:pure_term)
  : list pure_term

val list_as_vprop (vps:list pure_term) : pure_term

val check_vprop_equiv
  (f:RT.fstar_top_env)
  (g:env)
  (vp1 vp2:pure_term)
  (vp1_typing:tot_typing f g vp1 Tm_VProp)
  : T.Tac (vprop_equiv f g vp1 vp2)

val try_frame_pre (#f:RT.fstar_top_env)
                  (#g:env)
                  (#t:term)
                  (#pre:pure_term)
                  (pre_typing: tot_typing f g pre Tm_VProp)
                  (#c:pure_comp { stateful_comp c })
                  (t_typing: src_typing f g t c)
  : T.Tac (c':pure_comp_st { comp_pre c' == pre } &
           src_typing f g t c')

val frame_empty (#f:RT.fstar_top_env)
                (#g:env)
                (#pre:pure_term)
                (pre_typing: tot_typing f g pre Tm_VProp)
                (#u:universe)
                (#ty:pure_term) 
                (ut:universe_of f g ty u)
                (t:term)
                (c0:pure_comp_st{ comp_pre c0 == Tm_Emp })
                (d:src_typing f g t c0)
  : T.Tac (c:pure_comp_st { comp_pre c == pre} &
           src_typing f g t c)

