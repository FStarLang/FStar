module HoleBy

open FStar.Tactics

let x : int = _ by (exact (`1); dump "test")

let _ = assert (x == 1)
