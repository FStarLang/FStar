module FStarC.TypeChecker.Primops.Eq
#push-options "--MLish --MLish_effect FStarC.Effect"
module Env = FStarC.TypeChecker.Env
open FStarC.TypeChecker.Primops.Base

val dec_eq_ops (_:Env.env_t) : list primitive_step

val prop_eq_ops (_:Env.env_t) : list primitive_step