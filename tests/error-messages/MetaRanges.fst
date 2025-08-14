module MetaRanges

open FStar.Tactics.Typeclasses { solve }

let basic (#[Tactics.V2.fail ""] x : int) : unit = ()

// Error should be on the _
[@@expect_failure]
let _ = basic #_

class deq (a : Type) = {
  ( =? ) : a -> a -> Type;
}

[@@expect_failure]
let _ = 1 =? 1

[@@expect_failure]
let _ = (=?) 1 1

// Error covers `(=?) #_`, since the next implicit is what fails
[@@expect_failure]
let _ = (=?) #_ 1 1

// Error should be on the second _
[@@expect_failure]
let _ = (=?) #_ #_ 1 1

// Error should be on the solve
[@@expect_failure]
let _ = (=?) #_ #solve 1 1
