module Pulse.Checker.Inference

open Pulse.Syntax
open Pulse.Typing

module T = FStar.Tactics
module R = FStar.Reflection

val try_inst_uvs_in_goal (f:R.env) (g:env)
                         (ctxt:term)
                         (goal:vprop)
  : T.Tac (list (term & term))

val infer (f:R.env) (g:env) (head:term) (t_head:term) (ctxt_pre:term)
  : T.Tac st_term

val apply_solution (sol:list (term & term)) (t:term)
  : term

val contains_uvar (t:term)
  : bool

val try_unify (f:R.env) (g:env) (l r:term)
  : T.Tac (list (term & term))










