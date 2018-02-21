module Ill1

open FStar.Tactics
assume val f : term -> int

let _ = assert_by_tactic True (tm <-- quote (fun x -> x + 1); exact (f tm))
