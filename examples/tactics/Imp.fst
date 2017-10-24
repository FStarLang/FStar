module Imp

open FStar.Tactics

(* Testing that intro works on implicits seamlessly *)

let f : int -> int = synth_by_tactic (b <-- intro;
                                      exact (return (pack (Tv_Var b))))
let g : #x:int -> int = synth_by_tactic (b <-- intro;
                                         exact (return (pack (Tv_Var b))))

let _ = assert (f 3 == 3)
let _ = assert (g #3 == 3)
