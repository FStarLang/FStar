module UnitTests.Test

open FStar.Tactics
open UnitTests

let _ = assert_by_tactic True (fun () -> let i = testnat 42 in ())
