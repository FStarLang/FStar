module FStarMode_GH73
open FStar.Tactics

let x: bool = synth_by_tactic (fun () -> exact (quote 1))
