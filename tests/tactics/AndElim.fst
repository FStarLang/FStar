module AndElim

open FStar.Tactics.V2

assume val p : prop
assume val q : prop

let test (x : (p /\ q)) =
  assert True by (
    and_elim (quote x)
  )
