module Pulse.Prover.ElimExists

open Pulse.Syntax
open Pulse.Typing

open Pulse.Prover.Common

module T = FStar.Tactics.V2

val elim_exists (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt tm_vprop)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' tm_vprop &
            continuation_elaborator g ctxt g' ctxt')

val elim_exists_pst (#preamble:_) (pst:prover_state preamble)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst })
