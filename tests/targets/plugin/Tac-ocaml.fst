module Tac

open FStar.Tactics.V2

[@@plugin]
let prove_it () : Tac unit = trivial ()
