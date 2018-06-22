module Easy

open FStar.Tactics
open FStar.Tactics.Typeclasses

let easy_synth () =
    let _ = repeat intro in
    smt ()

val easy : (#[easy_synth] x : 'a) -> 'a
let easy x = x

val plus_assoc : x:int -> y:int -> z:int -> squash ((x + y) + z == x + (y + z))
let plus_assoc = easy

val plus_comm : x:int -> y:int -> squash (x + y == y + x)
let plus_comm = easy
