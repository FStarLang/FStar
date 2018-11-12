module LeftToRight

open FStar.Tactics

assume val a : int
assume val b : int
assume val c : int

assume val lem1 : unit -> Lemma (a + a == b)
assume val lem2 : unit -> Lemma (b + a == c)
assume val lem3 : unit -> Lemma (a + b == c)

let tau () : Tac unit =
    l_to_r [`lem1; `lem2; `lem3]

let _ = assert ((a + a) + a == c) by (tau (); trefl ())
let _ = assert ((a + a) == b) by (tau (); trefl ())
let _ = assert ((b + a) == c) by (tau (); trefl ())
let _ = assert ((a + b) == c) by (tau (); trefl ())
let _ = assert ((a + b) == c) by (tau (); trefl ())
