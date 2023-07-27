module Pulse.Checker.Prover.IntroExists

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Prover.Base

val intro_exists (#preamble:_) (pst:prover_state preamble)
  (u:universe) (b:binder) (body:vprop)
  (unsolved':list vprop)
  (_:squash (pst.unsolved == (tm_exists_sl u b body)::unsolved'))
  (prover:prover_t)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        is_terminal pst' })