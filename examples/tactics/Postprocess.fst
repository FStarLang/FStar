module Postprocess

open FStar.Tactics

let lem () : Lemma (1 == 2) = admit ()
let tau () = apply_lemma (`lem)

[@(postprocess_with tau)]
let x : int = 1

[@(postprocess_for_extraction_with tau)]
let y : int = 1

let _ = assert (x == 2)
let _ = assert (y == 1) // but `2` in extracted code
