module Pulse.Main

(* Model implementation of Pulse.Main: verified, but never extracted.
   The real implementation is the Pulse checker plugin (pulse/src/checker),
   which is not verified as part of the library. These tactics just fail. *)
module T = FStar.Tactics.V2

let check_pulse _ _ _ _ _ _ _ = fun _ -> T.fail "Pulse.Main model"

let check_pulse_after_desugar _ = fun _ -> T.fail "Pulse.Main model"
