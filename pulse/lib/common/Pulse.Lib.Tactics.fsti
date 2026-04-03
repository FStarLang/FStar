module Pulse.Lib.Tactics

open FStar.Tactics.Effect

[@@plugin]
val non_info_tac () : Tac unit
