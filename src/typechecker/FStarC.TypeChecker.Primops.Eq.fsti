module FStarC.TypeChecker.Primops.Eq
open FStarC.Effect
module Env = FStarC.TypeChecker.Env
open FStarC.TypeChecker.Primops.Base

val dec_eq_ops (_:Env.env_t) : ML (list primitive_step)

val prop_eq_ops (_:Env.env_t) : ML (list primitive_step)