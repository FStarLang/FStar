module TacF

open FStar.Tactics

(* Not exhaustive! But we're in TacF, so it's accepted *)
let tau i () : TacF unit =
    match i with
    | 42 -> exact (`())

(* If we call it just right, it works *)
let u : unit = synth_by_tactic (tau 42)
