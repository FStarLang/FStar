module Pulse.Checker.Inference

open Pulse.Syntax
open Pulse.Typing

module T = FStar.Tactics
module R = FStar.Reflection

val uvar_id : eqtype

val is_uvar (t:term) : option uvar_id

val gen_uvar (_:unit) : T.Tac (r:(uvar_id & term){Some? (is_uvar (snd r)) /\
                                                  Some?.v (is_uvar (snd r)) == fst r})

val try_inst_uvs_in_goal (ctxt:term)
                         (goal:vprop)
  : T.Tac (list (uvar_id & term))

val infer (head:term) (t_head:term) (ctxt_pre:term) (r:range)
  : T.Tac st_term

val apply_solution (sol:list (uvar_id & term)) (t:term)
  : term

val contains_uvar (t:term)
  : bool

val try_unify (l r:term)
  : T.Tac (list (uvar_id & term))
