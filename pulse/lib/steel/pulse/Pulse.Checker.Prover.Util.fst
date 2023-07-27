module Pulse.Checker.Prover.Util

module RU = Pulse.RuntimeUtils

let debug_prover g s =
  if RU.debug_at_level (fstar_env g) "prover"
  then T.print (s ())
  else ()
  