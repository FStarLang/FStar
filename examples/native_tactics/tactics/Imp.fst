module Imp

open FStar.Tactics

(* Testing that intro works on implicits seamlessly *)

[@plugin]
let tau () : Tac unit =
    let b = intro () in
    exact (pack (Tv_Var (bv_of_binder b)))

let f :    int -> int = synth_by_tactic tau
let g : #x:int -> int = synth_by_tactic tau

let _ = assert (f  3 == 3)
let _ = assert (g #3 == 3)
