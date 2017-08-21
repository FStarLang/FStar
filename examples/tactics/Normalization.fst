module Normalization

open FStar.Tactics

let normalize (steps: list norm_step) (#t:Type) (x:t) : tactic unit =
  dup;;
  exact (quote x);;
  norm steps;;
  trefl

let add_1 (x:int) : int = x + 1

// add_2 is defined to be x + 1 + 1
let add_2 (x:int) : int = synth_by_tactic (normalize [Delta; Primops] (add_1 (add_1 x)))

let four : int = synth_by_tactic (normalize [Delta; Primops] (add_2 2))

let _ = assert (four == 4)

let four' : int = synth_by_tactic (normalize [Delta] (add_2 2))

// four' has add_2 unfolded but the primitive addition is not performed
let _ = assert (four' == 2 + 1 + 1)

// note that UnfoldOnly modifies the effect of the Delta reduction step and has
// no effect on its own
let unfold_add_1: norm_step = UnfoldOnly [pack_fv ["Normalization"; "add_1"]]

let three : int = synth_by_tactic
  (normalize [Delta; unfold_add_1; Primops] (add_2 (add_1 0)))

let _ = assert (three == add_2 1)
