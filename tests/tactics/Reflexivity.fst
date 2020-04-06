module Reflexivity

open FStar.Tactics

let _ = assert (1 = 1)   by trefl ()
let _ = assert (1 == 1)  by trefl ()
(* sigh, (===) is not eq3 *)
let _ = assert (1 `eq3` 1) by trefl ()
let _ = assert (1 === 1) by (norm [delta]; trefl ())
