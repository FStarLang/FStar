module Pulse.Checker.Inference

open Pulse.Syntax

module T = FStar.Tactics

val infer (head:term) (t_head:term) (ctxt_pre:term)
  : T.Tac st_term
