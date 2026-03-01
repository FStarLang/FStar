module FStarC.TypeChecker.Primops.Erased
#push-options "--MLish --MLish_effect FStarC.Effect"

open FStarC.TypeChecker.Primops.Base

val ops : list primitive_step
val simplify_ops : list primitive_step
