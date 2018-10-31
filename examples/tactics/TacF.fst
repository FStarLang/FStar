module TacF

open FStar.Tactics

(* Not exhaustive! But we're in TacF, so it's accepted *)
let tau i : TacF unit =
    match i with
    | 42 -> exact (`())

(* If we call it just right, it even works *)
let u : unit = synth_by_tactic (fun () -> assume_safe (fun () -> tau 42))

let foo (x:int) : Tac unit = exact (`())

[@expect_failure]
let test1 (a:Type) (x:a) : unit = _ by (foo x)

let test2 (a:Type) (x:a) : unit = _ by (assume_safe (fun () -> foo x))
