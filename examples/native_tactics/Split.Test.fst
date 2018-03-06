module Split.Test
open FStar.Tactics
open Split

let test = 
  assert_by_tactic (True /\ True) compiled_split



