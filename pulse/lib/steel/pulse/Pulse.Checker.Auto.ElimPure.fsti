module Pulse.Checker.Auto.ElimPure

open Pulse.Syntax
open Pulse.Typing

open Pulse.Checker.Common
open Pulse.Checker.Auto.Elims

module T = FStar.Tactics.V2


val elim_pure (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt tm_vprop)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' tm_vprop &
            continuation_elaborator g ctxt g' ctxt')
