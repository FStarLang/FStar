module Ill1

open FStar.Tactics
assume val f : term -> int

[@(fail_errs [23])]
let _ = assert_by_tactic True (fun () -> let tm = quote (fun x -> x + 1) in
                                         exact (quote (f tm)))
