module Ill2

open FStar.Tactics
assume val f : term -> int

[@(Pervasives.fail [228])]
let _: int =
  synth_by_tactic
    (fun () -> let tm = quote (fun x -> x + 1) in
               exact (quote (f tm)))
