module Ill1

open FStar.Tactics
assume val f : term -> int

let _ = assert_by_tactic True (fun () -> let tm = quote (fun x -> x + 1) in
                                         exact (f tm))
