module Reflexivity

open FStar.Tactics

let _ = assert (1 = 1)   by trefl ()
let _ = assert (1 == 1)  by trefl ()
let _ = assert (1 === 1) by (norm [delta]; split (); trefl (); trefl ())
