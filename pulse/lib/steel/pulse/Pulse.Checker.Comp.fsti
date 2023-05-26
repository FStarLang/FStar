module Pulse.Checker.Comp

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common

val check_comp (g:env) 
               (c:comp_st)
               (pre_typing:tot_typing g (comp_pre c) Tm_VProp)
  : T.Tac (comp_typing g c (comp_u c))
