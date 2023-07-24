module Pulse.Checker.Prover.ElimPure

open Pulse.Syntax
open Pulse.Typing

open Pulse.Checker.Base
open Pulse.Checker.Prover.Base

module T = FStar.Tactics.V2


val elim_pure (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt tm_vprop)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' tm_vprop &
            continuation_elaborator g ctxt g' ctxt')

val elim_pure_pst (#preamble:_) (pst:prover_state preamble)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        pst'.unsolved == pst.unsolved })