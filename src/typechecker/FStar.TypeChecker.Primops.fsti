module FStar.TypeChecker.Primops

include FStar.TypeChecker.Primops.Base

(* This module just contains the list of all builtin primitive steps
with their implementations. *)

val built_in_primitive_steps_list : list primitive_step
val equality_ops_list (env:Env.env_t)  : list primitive_step
val env_dependent_ops (env:Env.env_t) : list primitive_step