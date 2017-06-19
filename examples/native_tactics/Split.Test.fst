module Split.Test
open FStar.Tactics
open Split

let test = 
  assert_by_tactic (compiled_split())  (True /\ False)



