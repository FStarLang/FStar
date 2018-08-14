module Admit

open FStar.Tactics

val l : x:int -> y:int -> squash (x + y == x + x)
let l x y = admit_dump ()

val l' : x:int -> y:int -> Lemma (x + y == x + x)
let l' x y = admit_dump ()

val x : r:int{False}
let x = magic_dump ()
