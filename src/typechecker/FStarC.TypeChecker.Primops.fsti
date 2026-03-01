module FStarC.TypeChecker.Primops

open FStarC.Effect
include FStarC.TypeChecker.Primops.Base

(* This module just contains the list of all builtin primitive steps
with their implementations. *)

(* Proper primitive steps. Some of them depend on the environment,
we put those in a separate list so the independent set can be
precomputed into a hash table. *)
val built_in_primitive_steps_list : list primitive_step
val env_dependent_ops (env:Env.env_t) : list primitive_step

(* Simplification rules. *)
val simplification_ops_list (env:Env.env_t)  : list primitive_step
