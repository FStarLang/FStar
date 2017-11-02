module Admit

open FStar.Tactics

val l : x:int -> y:int -> squash (x + y == x + x)
let l x y = admit_goal ()

val l' : x:int -> y:int -> Lemma (x + y == x + x)
let l' x y = admit_goal ()
