module FStarC.TypeChecker.Primops.MachineInts

open FStarC.TypeChecker.Primops.Base

val ops : list primitive_step

(* Simplification steps deciding [FStar.UInt.size x n] and [FStar.Int.size x n]
   on integer constants. *)
val simplify_ops : list primitive_step
