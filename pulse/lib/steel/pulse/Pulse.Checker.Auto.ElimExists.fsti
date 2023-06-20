module Pulse.Checker.Auto.ElimExists
open Pulse.Syntax
open Pulse.Typing

open Pulse.Checker.Common
open Pulse.Checker.Auto.Elims

module T = FStar.Tactics

val elim_exists (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt tm_vprop)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' tm_vprop &
            continuation_elaborator g ctxt g' ctxt')
