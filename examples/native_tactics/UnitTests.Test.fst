module UnitTests.Test

open FStar.Tactics
open UnitTests

let _ = assert_by_tactic True (testnat 42)
