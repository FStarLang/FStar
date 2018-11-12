module Ill1

open FStar.Tactics
assume val f : term -> int

[@(expect_failure [228])]
let _ = assert_by_tactic True (fun () -> let tm = quote (fun x -> x + 1) in
                                         exact (quote (f tm)))
