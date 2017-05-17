module A

open FStar.Tactics
//

let _ = assert_norm (True /\ True)

// This works because of explicit stopping the normalizer in tactics
let _ = assert_by_tactic (simpl) (True /\ True)

let _ = assert (c_and True True)

let _ = assert (c_and c_True c_True)
