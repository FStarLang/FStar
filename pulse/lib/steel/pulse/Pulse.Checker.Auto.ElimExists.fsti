module Pulse.Checker.Auto.ElimExists
open Pulse.Syntax
open Pulse.Checker.Common
open Pulse.Typing
module T = FStar.Tactics

val elim_exists (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt')