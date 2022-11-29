module SMTSync

open FStar.Tactics

let test1 x = assert (1 + x == x + 1)
  by (try smt_sync () with |_ -> fail "")

[@@expect_failure]
let test2 x = assert (1 + x == x + 2)
  by (try smt_sync () with |_ -> fail "")

let test3 x = assert (1 + x == x + 2)
  by (try smt_sync () with |_ -> tadmit ())
