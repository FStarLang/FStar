module Normalization

open FStar.Tactics

let normalize (#t:Type) (x:t) : tactic unit =
  dup;;
  exact (quote x);;
  norm [Delta; Primops];;
  trefl

let add_1 (x:int) : int = x + 1

// add_2 is defined to be x + 1 + 1
let add_2 (x:int) : int = synth_by_tactic (normalize (add_1 (add_1 x)))

let four : int = synth_by_tactic (normalize (add_2 2))

let _ = assert (four == 4)

let normalize_noprim (#t:Type) (x:t) : tactic unit =
  dup;;
  exact (quote x);;
  norm [Delta];;
  trefl

let four' : int = synth_by_tactic (normalize_noprim (add_2 2))

// four' has add_2 unfolded but the primitive addition is not performed
let _ = assert (four' == 2 + 1 + 1)

let normalize_add_1 (#t:Type) (x:t) : tactic unit =
  dup;;
  exact (quote x);;
  // note that UnfoldOnly modifies the effect of the Delta reduction step and
  // has no effect on its own
  norm [Delta; UnfoldOnly [pack_fv ["Normalization"; "add_1"]]; Primops];;
  trefl

let three : int = synth_by_tactic (normalize_add_1 (add_2 (add_1 0)))

let _ = assert (three == add_2 1)

// we can wrap up normalization and synthesis in a single "function" that
// returns its argument after normalization
let normalized (#t:Type) (x:t) : t =
  synth_by_tactic #t #unit (normalize x)

let four'' : int = normalized (2+2)

let _ = assert (four'' == 4)
