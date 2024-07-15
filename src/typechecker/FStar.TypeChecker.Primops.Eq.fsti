module FStar.TypeChecker.Primops.Eq
module Env = FStar.TypeChecker.Env
open FStar.TypeChecker.Primops.Base

val dec_eq_ops (_:Env.env_t) : list primitive_step

val prop_eq_ops (_:Env.env_t) : list primitive_step