module Unresolved

open FStar.Tactics

let tau : tactic unit =
    w <-- cur_witness;
    exact (return w)

let _ = assert_by_tactic tau False
