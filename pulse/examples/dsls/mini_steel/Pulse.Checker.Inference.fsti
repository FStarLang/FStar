module Pulse.Checker.Inference

open Pulse.Syntax

module T = FStar.Tactics

val try_inst_uvs_in_goal (uvs:list term)
                         (ctxt:term)
                         (goal:vprop)
  : T.Tac (list (term & term))

val infer (head:term) (t_head:term) (ctxt_pre:term)
  : T.Tac st_term
