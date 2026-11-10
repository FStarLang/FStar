module FStarC.TypeChecker.Primops

open FStarC.Effect
include FStarC.TypeChecker.Primops.Base

(* This module just contains the list of all builtin primitive steps
with their implementations. *)

(* Proper primitive steps. Some of them depend on the environment,
we put those in a separate list so the independent set can be
precomputed into a hash table. *)
val built_in_primitive_steps_list : list primitive_step
val env_dependent_ops (env:Env.env_t) : ML (list primitive_step)

(* The names of the steps in [env_dependent_ops]. *)
val env_dependent_op_lids : list FStarC.Ident.lident

(* The step in [env_dependent_ops env] named [l], if any. Cheap when [l]
is not in [env_dependent_op_lids]. *)
val env_dependent_op (env:Env.env_t) (l:FStarC.Ident.lident) : ML (option primitive_step)

(* Simplification rules. *)
val simplification_ops_list (env:Env.env_t) : ML (list primitive_step)
