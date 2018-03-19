module Unresolved

open FStar.Tactics

let tau () : Tac unit =
    let w = cur_witness () in
    exact w

let _ = assert_by_tactic False tau
