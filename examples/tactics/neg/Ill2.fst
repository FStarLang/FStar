module Ill2

open FStar.Tactics
assume val f : term -> int

let _: int =
  synth_by_tactic
    (tm <-- quote (fun x -> x + 1);
     exact (f tm))
