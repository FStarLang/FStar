module Unresolved

open FStar.Tactics

let tau () : Tac unit =
    let w = cur_witness () in
    exact w

[@(Pervasives.fail [217])]
let _ = assert_by_tactic False tau
