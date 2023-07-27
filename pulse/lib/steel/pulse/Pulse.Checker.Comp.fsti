module Pulse.Checker.Comp

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing

val check (g:env) 
          (c:comp_st)
          (pre_typing:tot_typing g (comp_pre c) tm_vprop)
  : T.Tac (comp_typing g c (comp_u c))
