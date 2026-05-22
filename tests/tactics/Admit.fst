module Admit

open FStar.Tactics.V2

#push-options "--lax"
let test () : False =
  _ by (
    ()
  )
#pop-options

[@@expect_failure [19]]
let test2 () : False =
  _ by (
    ()
  )
