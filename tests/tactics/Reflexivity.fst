module Reflexivity

open FStar.Tactics

let _ = assert (1 = 1)   by trefl ()
let _ = assert (1 == 1)  by trefl ()
let _ = assert (1 === 1) by (norm [delta]; split (); trefl (); trefl ())

let _ = assert (1 = 1)   by (compute(); trefl ())
let _ = assert (1 == 1)  by (compute(); trefl ())
let _ = assert (1 === 1) by (compute(); split (); trefl (); trefl ())

let _ = assert (x:unit{(fun x y -> equals x y) 1 1}) by trefl ()
