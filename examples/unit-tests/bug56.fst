module BugXX

val g : x:'a -> Lemma (ensures True)
let g x = ()

val xxx : x:nat -> y:nat -> Lemma (ensures (x=y))
let rec xxx x y = g (xxx y)
