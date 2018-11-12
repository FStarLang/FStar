module FailRange
open FStar.Tactics

let a : unit =
  assert_by_tactic (True /\ True)
    (fun () -> split (); fail "A")

let b () : unit =
  assert_by_tactic (True /\ True)
    (fun () -> split (); fail "B")

let c : unit =
  assert_by_tactic (True /\ True)
    (fun () -> fail "C")

let d () : unit =
  assert_by_tactic (True /\ True)
    (fun () -> fail "D")
