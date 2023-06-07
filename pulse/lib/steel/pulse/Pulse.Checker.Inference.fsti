module Pulse.Checker.Inference

open Pulse.Syntax
open Pulse.Typing

module T = FStar.Tactics
module R = FStar.Reflection
module RT = FStar.Reflection.Typing

val uvar_id : eqtype

let solution = list (uvar_id & term)

val uvar_id_to_string (_:uvar_id) : string

val is_uvar (t:term) : option uvar_id

val gen_uvar (name:ppname)
  : T.Tac (r:(uvar_id & term){
            is_uvar (snd r) == Some (fst r)
          })

val try_inst_uvs_in_goal (ctxt:term)
                         (goal:vprop)
  : T.Tac solution

val infer (head:term) (t_head:term) (ctxt_pre:term) (r:range)
  : T.Tac st_term

val solutions_to_string (sol:solution)
  : T.Tac string

val apply_solution (sol:solution) (t:term)
  : term

val contains_uvar (t:term)
  : bool

val try_unify (l r:term)
  : T.Tac solution

val try_solve_pure_equalities (p:term)
  : T.Tac solution