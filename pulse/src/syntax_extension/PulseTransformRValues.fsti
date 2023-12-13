module PulseTransformRValues
module Sugar = PulseSugar
open PulseErr

val transform (_:PulseEnv.env_t) (p:Sugar.stmt)
  : err Sugar.stmt
