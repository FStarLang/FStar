module Admit

open FStar.Tactics.V2

#push-options "--admit_smt_queries true"
let test () : squash False =
  _ by (
    ()
  )
#pop-options

[@@expect_failure [19]]
let test2 () : squash False =
  _ by (
    ()
  )
