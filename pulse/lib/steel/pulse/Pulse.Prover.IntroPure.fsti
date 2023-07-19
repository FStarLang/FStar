module Pulse.Prover.IntroPure

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Prover.Common

val intro_pure (#preamble:_) (pst:prover_state preamble)
  (t:term)
  (unsolved':list vprop)
  (_:squash (pst.unsolved == (tm_pure t)::unsolved'))
  : T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst }))
