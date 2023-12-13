module PulseSyntaxExtension.TransformRValues
module Sugar = PulseSyntaxExtension.Sugar
module Err = PulseSyntaxExtension.Err
module PulseEnv = PulseSyntaxExtension.Env
val transform (_:PulseEnv.env_t) (p:Sugar.stmt)
  : Err.err Sugar.stmt
