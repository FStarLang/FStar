module Pulse.Checker.Inference

open Pulse.Syntax
open Pulse.Typing

module T = FStar.Tactics
module R = FStar.Reflection
module RT = FStar.Reflection.Typing

val uvar : Type0

val uvar_eq (u1 u2:uvar) : b:bool { b <==> (u1 == u2) }

let solution = list (uvar & term)

val uvar_to_string (_:uvar) : T.Tac string

val range_of_uvar (_:uvar) : range

val is_uvar (t:term) : option uvar

val gen_uvar (name:ppname)
  : T.Tac (r:(uvar & term){
            is_uvar (snd r) == Some (fst r)
          })

val find_solution (sol:solution) (u:uvar) : option term

val try_inst_uvs_in_goal (g:env) (ctxt:term)
                         (goal:vprop)
  : T.Tac solution

val infer (g:env) (head:term) (t_head:term) (ctxt_pre:term) (r:range)
  : T.Tac st_term

val solutions_to_string (sol:solution)
  : T.Tac string

val apply_solution (sol:solution) (t:term)
  : T.Tac term

val contains_uvar (t:term)
  : T.Tac bool

val try_unify (g:env) (l r:term)
  : T.Tac solution

val try_solve_pure_equalities (g:env) (p:term)
  : T.Tac solution